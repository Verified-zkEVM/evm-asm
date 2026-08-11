/-
  ExecutionRequestsHashHashOneLa — la blob + SB type for erh_hash_one.
  Parent: #12011 option B. Residual h_sha discharge owner #12018.
-/
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOne
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneBody

namespace EvmAsm.Codegen.ExecutionRequestsHashHashOneLa

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.ExecutionRequestsHashHashOne
open EvmAsm.Codegen.ExecutionRequestsHashHashOneBody

set_option maxRecDepth 8000

private theorem la_blob_hi8 :
    laHi GuestAddrs.erh_blob (GuestAddrs.erh_hash_one + 8) =
      Rv64.laHi (B1 + 8) Blob := by decide

private theorem la_blob_lo8 :
    laLo GuestAddrs.erh_blob (GuestAddrs.erh_hash_one + 8) =
      Rv64.laLo (B1 + 8) Blob := by decide

private theorem la_blob_range8 : laInRange (B1 + 8) Blob := by decide

private theorem blob_aligned : Blob.toNat % 8 = 0 := by decide

private theorem ho_ins2 :
    hoProgL[2]'(by rw [hoProgL_len]; norm_num) =
      .AUIPC .x5 (laHi GuestAddrs.erh_blob (GuestAddrs.erh_hash_one + 8)) := by
  decide

private theorem ho_ins3 :
    hoProgL[3]'(by rw [hoProgL_len]; norm_num) =
      .ADDI .x5 .x5 (laLo GuestAddrs.erh_blob (GuestAddrs.erh_hash_one + 8)) := by
  decide

private theorem ho_ins4 :
    hoProgL[4]'(by rw [hoProgL_len]; norm_num) =
      .SB .x5 .x14 (0 : BitVec 12) := by
  decide

private theorem hpc2 : pc 2 = B1 + 8 := by simp only [pc]; decide
private theorem hpc3 : pc 3 = B1 + 12 := by simp only [pc]; decide
private theorem hpc4 : pc 4 = B1 + 16 := by simp only [pc]; decide
private theorem hpc24 : (pc 2 : Word) + 8 = pc 4 := by simp only [pc]; decide
private theorem hpc45 : (pc 4 : Word) + 4 = pc 5 := by simp only [pc]; decide
private theorem hpc23 : (pc 2 : Word) + 4 = pc 3 := by simp only [pc]; decide

/-- la x5, erh_blob. Fuel 2. pc2→pc4. -/
theorem hash_one_la_blob
    (newSp raVal bodyPtr typeW lenW destPtr v5old : Word)
    (body blobBytes outBytes : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 2 (pc 2) (pc 4) fullCodeHo
      ((.x5 ↦ᵣ v5old) **
        hoAfterPrologue newSp raVal bodyPtr typeW lenW destPtr
          body blobBytes outBytes A)
      ((.x5 ↦ᵣ Blob) **
        hoAfterPrologue newSp raVal bodyPtr typeW lenW destPtr
          body blobBytes outBytes A) := by
  have hIn := hoInputs_pcFree bodyPtr typeW lenW destPtr body blobBytes outBytes A hA
  have hla := la_materialize_within (cr := fullCodeHo) .x5 v5old (pc 2) Blob
    (by decide) la_blob_range8
    (by
      intro a i hs
      -- AUIPC uses Codegen.laHi; la_materialize emits Rv64.laHi
      have hs' : CodeReq.singleton (pc 2)
          (.AUIPC .x5 (laHi GuestAddrs.erh_blob (GuestAddrs.erh_hash_one + 8)))
          a = some i := by
        simpa [la_blob_hi8] using hs
      exact mem_at 2 _ (pc 2) hpc2 (by rw [hoProgL_len]; norm_num) ho_ins2 a i hs')
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 3)
          (.ADDI .x5 .x5 (laLo GuestAddrs.erh_blob (GuestAddrs.erh_hash_one + 8)))
          a = some i := by
        simpa [hpc23, la_blob_lo8] using hs
      exact mem_at 3 _ (pc 3) hpc3 (by rw [hoProgL_len]; norm_num) ho_ins3 a i hs')
  rw [hpc24] at hla
  have hlaF := cpsTripleWithin_frameR
    (hoAfterPrologue newSp raVal bodyPtr typeW lenW destPtr
      body blobBytes outBytes A)
    (by
      simp only [hoAfterPrologue]
      exact pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj (pcFree_frameSlotsSaved _ _ _) hIn)))
    hla
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) hlaF

/-- After SB type: blob[0] = typeByte. -/
def hoAfterType (newSp raVal bodyPtr typeW lenW destPtr : Word)
    (body blobTail outBytes : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
  frameSlotsSaved hoFrame newSp (hoVals raVal) **
  (.x5 ↦ᵣ Blob) **
  (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ lenW) ** (.x24 ↦ᵣ destPtr) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion bodyPtr body **
  bytesRegion Blob (typeByte typeW :: blobTail) **
  bytesRegion destPtr outBytes ** A

private theorem typeByte_eq_truncate (typeW : Word) :
    typeW.truncate 8 = typeByte typeW := by
  simp only [typeByte, BitVec.truncate_eq_setWidth, BitVec.ofNat_toNat]

/-- SB type at blob[0]. Fuel 1. pc4→pc5.
    Pre: x5=Blob, blob = b0::tail. -/
theorem hash_one_sb_type
    (newSp raVal bodyPtr typeW lenW destPtr : Word)
    (body blobTail outBytes : List (BitVec 8))
    (b0 : BitVec 8)
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 1 (pc 4) (pc 5) fullCodeHo
      ((.x5 ↦ᵣ Blob) **
        hoAfterPrologue newSp raVal bodyPtr typeW lenW destPtr
          body (b0 :: blobTail) outBytes A)
      (hoAfterType newSp raVal bodyPtr typeW lenW destPtr
        body blobTail outBytes A) := by
  have hIn := hoInputs_pcFree bodyPtr typeW lenW destPtr
    body (b0 :: blobTail) outBytes A hA
  have hzero : Blob + BitVec.ofNat 64 0 = Blob := BitVec.add_zero _
  have hsb := bytesRegion_sb_within .x5 .x14 Blob typeW (pc 4) (b0 :: blobTail) 0
    blob_aligned (Nat.zero_lt_succ _)
    (by have := Blob.isLt; omega)
    (by decide)
  have hsb' : cpsTripleWithin 1 (pc 4) (pc 4 + 4)
      (CodeReq.singleton (pc 4) (.SB .x5 .x14 0))
      ((.x5 ↦ᵣ Blob) ** (.x14 ↦ᵣ typeW) ** bytesRegion Blob (b0 :: blobTail))
      ((.x5 ↦ᵣ Blob) ** (.x14 ↦ᵣ typeW) **
        bytesRegion Blob ((b0 :: blobTail).set 0 (typeW.truncate 8))) := by
    simpa [hzero] using hsb
  have hsbC := cpsTripleWithin_extend_code
    (mem_at 4 _ (pc 4) hpc4 (by rw [hoProgL_len]; norm_num) ho_ins4)
    hsb'
  rw [hpc45] at hsbC
  have hset : (b0 :: blobTail).set 0 (typeW.truncate 8) =
      typeByte typeW :: blobTail := by
    simp [List.set, typeByte_eq_truncate]
  have hsbF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
      frameSlotsSaved hoFrame newSp (hoVals raVal) **
      (.x13 ↦ᵣ bodyPtr) ** (.x26 ↦ᵣ lenW) ** (.x24 ↦ᵣ destPtr) **
      (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion bodyPtr body **
      bytesRegion destPtr outBytes ** A)
    (by
      repeat' first
        | exact bytesRegion_pcFree _ _
        | exact pcFree_regIs
        | exact pcFree_frameSlotsSaved _ _ _
        | apply pcFree_sepConj
        | exact hA)
    hsbC
  refine cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [hoAfterPrologue, hoInputs] at hp
      xperm_chunked hp)
    (fun _ hq => by
      simp only [hoAfterType, hset] at hq ⊢
      xperm_chunked hq)
    hsbF

/-- Compose la + SB type. Fuel 3. pc2→pc5. -/
theorem hash_one_la_sb_type
    (newSp raVal bodyPtr typeW lenW destPtr v5old : Word)
    (body blobTail outBytes : List (BitVec 8))
    (b0 : BitVec 8)
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 3 (pc 2) (pc 5) fullCodeHo
      ((.x5 ↦ᵣ v5old) **
        hoAfterPrologue newSp raVal bodyPtr typeW lenW destPtr
          body (b0 :: blobTail) outBytes A)
      (hoAfterType newSp raVal bodyPtr typeW lenW destPtr
        body blobTail outBytes A) := by
  have hla := hash_one_la_blob newSp raVal bodyPtr typeW lenW destPtr v5old
    body (b0 :: blobTail) outBytes A hA
  have hsb := hash_one_sb_type newSp raVal bodyPtr typeW lenW destPtr
    body blobTail outBytes b0 A hA
  exact cpsTripleWithin_seq_same_cr hla hsb

end EvmAsm.Codegen.ExecutionRequestsHashHashOneLa
