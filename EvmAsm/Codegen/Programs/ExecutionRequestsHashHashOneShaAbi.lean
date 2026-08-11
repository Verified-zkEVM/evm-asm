/-
  ExecutionRequestsHashHashOneShaAbi — empty-body sha ABI + residual call.

  Geometry pc15→pc20 (after empty BEQ):
    15-16 la a0, erh_blob
    17    ADDI a1, s10, 1
    18    MV a2, s8
    19    JAL zkvm_sha256  ← residual h_sha (#12018)

  Ambient carries stackFree newSp 6 (below frame; disjoint from
  frameSlotsSaved at newSp+0). Parent: #12011 option B. Owner #12018.
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
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.ExecutionRequestsHashShaResidual
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOne
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneBody
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneEmpty
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Stateless.SpecRef.Crypto

namespace EvmAsm.Codegen.ExecutionRequestsHashHashOneShaAbi

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.ExecutionRequestsHashShaResidual
open EvmAsm.Codegen.ExecutionRequestsHashHashOne
open EvmAsm.Codegen.ExecutionRequestsHashHashOneBody
open EvmAsm.Codegen.ExecutionRequestsHashHashOneEmpty
open EvmAsm.Stateless.SpecRef

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

private theorem ho_ins15 :
    hoProgL[15]'(by rw [hoProgL_len]; norm_num) =
      .AUIPC .x10 (laHi GuestAddrs.erh_blob (GuestAddrs.erh_hash_one + 60)) := by decide
private theorem ho_ins16 :
    hoProgL[16]'(by rw [hoProgL_len]; norm_num) =
      .ADDI .x10 .x10 (laLo GuestAddrs.erh_blob (GuestAddrs.erh_hash_one + 60)) := by decide
private theorem ho_ins17 :
    hoProgL[17]'(by rw [hoProgL_len]; norm_num) =
      .ADDI .x11 .x26 (1 : BitVec 12) := by decide
private theorem ho_ins18 :
    hoProgL[18]'(by rw [hoProgL_len]; norm_num) =
      .MV .x12 .x24 := by decide

private theorem hpc15 : pc 15 = B1 + 60 := by simp only [pc]; decide
private theorem hpc16 : pc 16 = B1 + 64 := by simp only [pc]; decide
private theorem hpc17 : pc 17 = B1 + 68 := by simp only [pc]; decide
private theorem hpc18 : pc 18 = B1 + 72 := by simp only [pc]; decide
private theorem hpc19 : pc 19 = B1 + 76 := by simp only [pc]; decide
private theorem hpc20 : pc 20 = B1 + 80 := by simp only [pc]; decide

private theorem hpc1516 : (pc 15 : Word) + 4 = pc 16 := by simp only [pc]; decide
private theorem hpc1517 : (pc 15 : Word) + 8 = pc 17 := by simp only [pc]; decide
private theorem hpc1718 : (pc 17 : Word) + 4 = pc 18 := by simp only [pc]; decide
private theorem hpc1819 : (pc 18 : Word) + 4 = pc 19 := by simp only [pc]; decide
private theorem hpc1920 : (pc 19 : Word) + 4 = pc 20 := by simp only [pc]; decide

private theorem se12_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide

private theorem la_blob_hi60 :
    laHi GuestAddrs.erh_blob (GuestAddrs.erh_hash_one + 60) =
      Rv64.laHi (pc 15) Blob := by simp only [pc]; decide
private theorem la_blob_lo60 :
    laLo GuestAddrs.erh_blob (GuestAddrs.erh_hash_one + 60) =
      Rv64.laLo (pc 15) Blob := by simp only [pc]; decide
private theorem la_blob_range60 : laInRange (pc 15) Blob := by
  simp only [pc]; decide

/-- After empty BEQ with stackFree under A (A_user is free of stack). -/
def hoAfterCopySetupSf (newSp raVal bodyPtr typeW lenW destPtr : Word)
    (body blobTail outBytes : List (BitVec 8)) (A : Assertion) : Assertion :=
  hoAfterCopySetup newSp raVal bodyPtr typeW lenW destPtr body blobTail outBytes
    (stackFree newSp 6 ** A)

/-- After sha ABI: a0=Blob a1=len+1 a2=dest + copy-setup ambient with sf. -/
def hoAfterShaAbi (newSp raVal bodyPtr typeW lenW destPtr : Word)
    (body blobBytes outBytes : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x10 ↦ᵣ Blob) ** (.x11 ↦ᵣ (lenW + (1 : Word))) ** (.x12 ↦ᵣ destPtr) **
  (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
  frameSlotsSaved hoFrame newSp (hoVals raVal) **
  stackFree newSp 6 **
  (.x5 ↦ᵣ Blob) ** (.x6 ↦ᵣ (Blob + (1 : Word))) **
  (.x7 ↦ᵣ bodyPtr) ** (.x28 ↦ᵣ lenW) **
  (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ lenW) ** (.x24 ↦ᵣ destPtr) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion bodyPtr body **
  bytesRegion Blob blobBytes **
  bytesRegion destPtr outBytes ** A

/-- Residual F: frame + temp owns + non-ABI path regs + body.
    Temps enter as owns (peeled from concrete pre-call values) and pass through
    the residual; shaCallReturn owns only ABI x10-12. -/
def hoShaResidualF (newSp raVal bodyPtr typeW lenW destPtr : Word)
    (body : List (BitVec 8)) (A : Assertion) : Assertion :=
  frameSlotsSaved hoFrame newSp (hoVals raVal) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ lenW) ** (.x24 ↦ᵣ destPtr) **
  bytesRegion bodyPtr body ** A

/-- la a0 + ADDI a1 + MV a2. Fuel 4. pc15→pc19. -/
theorem hash_one_sha_abi
    (newSp raVal bodyPtr typeW lenW destPtr v10old v11old v12old : Word)
    (body blobTail outBytes : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 4 (pc 15) (pc 19) fullCodeHo
      ((.x10 ↦ᵣ v10old) ** (.x11 ↦ᵣ v11old) ** (.x12 ↦ᵣ v12old) **
        hoAfterCopySetupSf newSp raVal bodyPtr typeW lenW destPtr
          body blobTail outBytes A)
      (hoAfterShaAbi newSp raVal bodyPtr typeW lenW destPtr body
        (typeByte typeW :: blobTail) outBytes A) := by
  -- la a0, erh_blob (fuel 2)
  have hla := la_materialize_within (cr := fullCodeHo) .x10 v10old (pc 15) Blob
    (by decide) la_blob_range60
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 15)
          (.AUIPC .x10 (laHi GuestAddrs.erh_blob (GuestAddrs.erh_hash_one + 60)))
          a = some i := by simpa [la_blob_hi60] using hs
      exact mem_at 15 _ (pc 15) hpc15 (by rw [hoProgL_len]; norm_num) ho_ins15 a i hs')
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 16)
          (.ADDI .x10 .x10 (laLo GuestAddrs.erh_blob (GuestAddrs.erh_hash_one + 60)))
          a = some i := by simpa [hpc1516, la_blob_lo60] using hs
      exact mem_at 16 _ (pc 16) hpc16 (by rw [hoProgL_len]; norm_num) ho_ins16 a i hs')
  rw [hpc1517] at hla
  let Fla : Assertion :=
    (.x11 ↦ᵣ v11old) ** (.x12 ↦ᵣ v12old) **
    hoAfterCopySetupSf newSp raVal bodyPtr typeW lenW destPtr
      body blobTail outBytes A
  have hFla : Fla.pcFree := by
    dsimp only [Fla, hoAfterCopySetupSf, hoAfterCopySetup]
    pcf; exact hA
  have hlaF := cpsTripleWithin_frameR Fla hFla hla
  have c_la : cpsTripleWithin 2 (pc 15) (pc 17) fullCodeHo
      ((.x10 ↦ᵣ v10old) ** (.x11 ↦ᵣ v11old) ** (.x12 ↦ᵣ v12old) **
        hoAfterCopySetupSf newSp raVal bodyPtr typeW lenW destPtr
          body blobTail outBytes A)
      ((.x10 ↦ᵣ Blob) ** (.x11 ↦ᵣ v11old) ** (.x12 ↦ᵣ v12old) **
        hoAfterCopySetupSf newSp raVal bodyPtr typeW lenW destPtr
          body blobTail outBytes A) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by dsimp only [Fla] at *; xperm_chunked hp)
      (fun _ hq => by dsimp only [Fla] at hq; xperm_chunked hq)
      hlaF
  -- ADDI a1, s10, 1
  have haddi := addi_spec_gen_within .x11 .x26 v11old lenW (1 : BitVec 12) (pc 17)
    (by decide)
  have haddiC := cpsTripleWithin_extend_code
    (mem_at 17 _ (pc 17) hpc17 (by rw [hoProgL_len]; norm_num) ho_ins17) haddi
  rw [hpc1718] at haddiC
  let F11 : Assertion :=
    (.x10 ↦ᵣ Blob) ** (.x12 ↦ᵣ v12old) **
    (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
    frameSlotsSaved hoFrame newSp (hoVals raVal) **
    stackFree newSp 6 **
    (.x5 ↦ᵣ Blob) ** (.x6 ↦ᵣ (Blob + (1 : Word))) **
    (.x7 ↦ᵣ bodyPtr) ** (.x28 ↦ᵣ lenW) **
    (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x24 ↦ᵣ destPtr) **
    (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion bodyPtr body **
    bytesRegion Blob (typeByte typeW :: blobTail) **
    bytesRegion destPtr outBytes ** A
  have hF11 : F11.pcFree := by dsimp only [F11]; pcf; exact hA
  have haddiF := cpsTripleWithin_frameR F11 hF11 haddiC
  have c_addi : cpsTripleWithin 1 (pc 17) (pc 18) fullCodeHo
      ((.x10 ↦ᵣ Blob) ** (.x11 ↦ᵣ v11old) ** (.x12 ↦ᵣ v12old) **
        hoAfterCopySetupSf newSp raVal bodyPtr typeW lenW destPtr
          body blobTail outBytes A)
      ((.x10 ↦ᵣ Blob) ** (.x11 ↦ᵣ (lenW + (1 : Word))) ** (.x12 ↦ᵣ v12old) **
        hoAfterCopySetupSf newSp raVal bodyPtr typeW lenW destPtr
          body blobTail outBytes A) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [F11] at *
        simp only [hoAfterCopySetupSf, hoAfterCopySetup] at hp ⊢
        xperm_chunked hp)
      (fun _ hq => by
        dsimp only [F11] at hq
        simp only [se12_1, hoAfterCopySetupSf, hoAfterCopySetup] at hq ⊢
        xperm_chunked hq)
      haddiF
  -- MV a2, s8
  have hmv := mv_spec_gen_within .x12 .x24 destPtr v12old (pc 18) (by decide)
  have hmvC := cpsTripleWithin_extend_code
    (mem_at 18 _ (pc 18) hpc18 (by rw [hoProgL_len]; norm_num) ho_ins18) hmv
  rw [hpc1819] at hmvC
  let F12 : Assertion :=
    (.x10 ↦ᵣ Blob) ** (.x11 ↦ᵣ (lenW + (1 : Word))) **
    (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
    frameSlotsSaved hoFrame newSp (hoVals raVal) **
    stackFree newSp 6 **
    (.x5 ↦ᵣ Blob) ** (.x6 ↦ᵣ (Blob + (1 : Word))) **
    (.x7 ↦ᵣ bodyPtr) ** (.x28 ↦ᵣ lenW) **
    (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ lenW) **
    (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion bodyPtr body **
    bytesRegion Blob (typeByte typeW :: blobTail) **
    bytesRegion destPtr outBytes ** A
  have hF12 : F12.pcFree := by dsimp only [F12]; pcf; exact hA
  have hmvF := cpsTripleWithin_frameR F12 hF12 hmvC
  have c_mv : cpsTripleWithin 1 (pc 18) (pc 19) fullCodeHo
      ((.x10 ↦ᵣ Blob) ** (.x11 ↦ᵣ (lenW + (1 : Word))) ** (.x12 ↦ᵣ v12old) **
        hoAfterCopySetupSf newSp raVal bodyPtr typeW lenW destPtr
          body blobTail outBytes A)
      (hoAfterShaAbi newSp raVal bodyPtr typeW lenW destPtr body
        (typeByte typeW :: blobTail) outBytes A) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [F12] at *
        simp only [hoAfterCopySetupSf, hoAfterCopySetup] at hp ⊢
        xperm_chunked hp)
      (fun _ hq => by
        dsimp only [F12, hoAfterShaAbi] at hq ⊢
        xperm_chunked hq)
      hmvF
  exact cpsTripleWithin_seq_same_cr c_la (cpsTripleWithin_seq_same_cr c_addi c_mv)

/-- Peel temps to owns then residual call. Fuel 1+shaResidualFuel. pc19→pc20. -/
theorem hash_one_sha_call_empty
    (newSp raVal bodyPtr typeW destPtr : Word)
    (body outOld : List (BitVec 8))
    (A : Assertion) (_hA : A.pcFree)
    (h_sha : shaCallWithinShape fullCodeHo (pc 19) raVal newSp
        Blob (1 : Word) destPtr
        (hashOneBlob (typeByte typeW) []) outOld
        (jalOff GuestAddrs.zkvm_sha256 (GuestAddrs.erh_hash_one + 76))
        shaResidualFuel
        (hoShaResidualF newSp raVal bodyPtr typeW (0 : Word) destPtr body A)) :
    cpsTripleWithin (1 + shaResidualFuel) (pc 19) (pc 20) fullCodeHo
      (hoAfterShaAbi newSp raVal bodyPtr typeW (0 : Word) destPtr body
        (typeByte typeW :: []) outOld A)
      (((.x1 ↦ᵣ (pc 20)) **
        shaCallReturn newSp Blob destPtr (hashOneBlob (typeByte typeW) [])) **
        hoShaResidualF newSp raVal bodyPtr typeW (0 : Word) destPtr body A) := by
  obtain ⟨_, _, _, _, _, _, hcall⟩ := h_sha
  have hpc : (pc 19 : Word) + 4 = pc 20 := hpc1920
  have h1 : (0 : Word) + (1 : Word) = (1 : Word) := by decide
  have hcall' : cpsTripleWithin (1 + shaResidualFuel) (pc 19) (pc 20) fullCodeHo
      (((.x1 ↦ᵣ raVal) **
        shaCallEntry newSp Blob (1 : Word) destPtr
          (hashOneBlob (typeByte typeW) []) outOld) **
        hoShaResidualF newSp raVal bodyPtr typeW (0 : Word) destPtr body A)
      (((.x1 ↦ᵣ (pc 20)) **
        shaCallReturn newSp Blob destPtr (hashOneBlob (typeByte typeW) [])) **
        hoShaResidualF newSp raVal bodyPtr typeW (0 : Word) destPtr body A) := by
    simpa [hpc] using hcall
  have hpre : ∀ h,
      (hoAfterShaAbi newSp raVal bodyPtr typeW (0 : Word) destPtr body
        (typeByte typeW :: []) outOld A) h →
      (((.x1 ↦ᵣ raVal) **
        shaCallEntry newSp Blob (1 : Word) destPtr
          (hashOneBlob (typeByte typeW) []) outOld) **
        hoShaResidualF newSp raVal bodyPtr typeW (0 : Word) destPtr body A) h := by
    intro h hp
    dsimp only [hoAfterShaAbi, shaCallEntry, hoShaResidualF, hashOneBlob] at hp ⊢
    simp only [h1] at hp
    have hx5 := @regIs_implies_regOwn (r := .x5) (v := Blob)
    have hx6 := @regIs_implies_regOwn (r := .x6) (v := Blob + (1 : Word))
    have hx7 := @regIs_implies_regOwn (r := .x7) (v := bodyPtr)
    have hx28 := @regIs_implies_regOwn (r := .x28) (v := (0 : Word))
    -- front four concrete temps
    have hp' :
        (((.x5 ↦ᵣ Blob) ** (.x6 ↦ᵣ (Blob + (1 : Word))) **
            (.x7 ↦ᵣ bodyPtr) ** (.x28 ↦ᵣ (0 : Word))) **
          ((.x10 ↦ᵣ Blob) ** (.x11 ↦ᵣ (1 : Word)) ** (.x12 ↦ᵣ destPtr) **
            (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
            frameSlotsSaved hoFrame newSp (hoVals raVal) **
            stackFree newSp 6 **
            (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ (0 : Word)) **
            (.x24 ↦ᵣ destPtr) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion bodyPtr body **
            bytesRegion Blob [typeByte typeW] **
            bytesRegion destPtr outOld ** A)) h := by
      xperm_chunked hp
    have hpDrop :
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28) **
          ((.x10 ↦ᵣ Blob) ** (.x11 ↦ᵣ (1 : Word)) ** (.x12 ↦ᵣ destPtr) **
            (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
            frameSlotsSaved hoFrame newSp (hoVals raVal) **
            stackFree newSp 6 **
            (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ (0 : Word)) **
            (.x24 ↦ᵣ destPtr) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion bodyPtr body **
            bytesRegion Blob [typeByte typeW] **
            bytesRegion destPtr outOld ** A)) h := by
      refine (sepConj_mono ?_ (fun _ hx => hx) _) hp'
      intro h' ht
      exact sepConj_mono hx5 (sepConj_mono hx6 (sepConj_mono hx7 hx28)) h' ht
    xperm_chunked hpDrop
  exact cpsTripleWithin_weaken hpre (fun _ hq => hq) hcall'

private theorem ho_ins21 :
    hoProgL[21]'(by rw [hoProgL_len]; norm_num) =
      .ADDI .x2 .x2 (16 : BitVec 12) := by decide
private theorem ho_ins22 :
    hoProgL[22]'(by rw [hoProgL_len]; norm_num) =
      .JALR .x0 .x1 (0 : BitVec 12) := by decide

private theorem hpc21 : pc 21 = B1 + 84 := by simp only [pc]; decide
private theorem hpc22 : pc 22 = B1 + 88 := by simp only [pc]; decide
private theorem hpc2021 : (pc 20 : Word) + BitVec.ofNat 64 (4 * hoFrame.length) = pc 21 := by
  simp only [hoFrame_length, pc]; decide
private theorem hpc2122 : (pc 21 : Word) + 4 = pc 22 := by simp only [pc]; decide
private theorem se12_16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide

private theorem frame_restore (sp0 : Word) :
    (sp0 + (-16 : Word)) + (16 : Word) = sp0 := by
  rw [BitVec.add_assoc]
  have h : (-16 : Word) + (16 : Word) = (0 : Word) := by decide
  rw [h]
  exact BitVec.add_zero sp0

/-- Empty-body exit ambient (everything except restored x1/x2). -/
def hoEmptyExitAmb (newSp bodyPtr typeW destPtr : Word)
    (body : List (BitVec 8)) (A : Assertion) : Assertion :=
  stackFree newSp 6 **
  regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ (0 : Word)) ** (.x24 ↦ᵣ destPtr) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion bodyPtr body **
  bytesRegion Blob (hashOneBlob (typeByte typeW) []) **
  bytesRegion destPtr (sha256 (hashOneBlob (typeByte typeW) [])) ** A

theorem hoEmptyExitAmb_pcFree (newSp bodyPtr typeW destPtr : Word)
    (body : List (BitVec 8)) (A : Assertion) (hA : A.pcFree) :
    (hoEmptyExitAmb newSp bodyPtr typeW destPtr body A).pcFree := by
  simp only [hoEmptyExitAmb]
  repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_stackFree _ _
    | exact pcFree_emp
    | apply pcFree_sepConj
    | exact hA

/-- Empty-body exit post: restored sp/ra, digest = sha256 [type], blob preserved. -/
def hoEmptyExitPost (sp0 raVal bodyPtr typeW destPtr : Word)
    (body : List (BitVec 8)) (A : Assertion) : Assertion :=
  let newSp := sp0 + (-16 : Word)
  (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) **
  frameSlotsSaved hoFrame newSp (hoVals raVal) **
  hoEmptyExitAmb newSp bodyPtr typeW destPtr body A

/-- Residual post reshaped for loadSeq: x2 ** regsAt (old ra=pc20) ** slots ** amb. -/
def hoEpiLoadPre (newSp raVal bodyPtr typeW destPtr : Word)
    (body : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x2 ↦ᵣ newSp) ** regsAt hoFrame (fun
      | .x1 => pc 20
      | _ => 0) **
    frameSlotsSaved hoFrame newSp (hoVals raVal) **
    hoEmptyExitAmb newSp bodyPtr typeW destPtr body A

/-- Epi LD/ADDI/JALR after residual. Fuel 3. pc20→raVal (ret).
    Requires `raVal` even. `newSp = sp0 + (-16)`. -/
theorem hash_one_epi_empty
    (sp0 raVal bodyPtr typeW destPtr : Word)
    (body : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (heven : (raVal &&& ~~~(1 : Word)) = raVal) :
    let newSp := sp0 + (-16 : Word)
    cpsTripleWithin 3 (pc 20) raVal fullCodeHo
      (((.x1 ↦ᵣ (pc 20)) **
        shaCallReturn newSp Blob destPtr (hashOneBlob (typeByte typeW) [])) **
        hoShaResidualF newSp raVal bodyPtr typeW (0 : Word) destPtr body A)
      (hoEmptyExitPost sp0 raVal bodyPtr typeW destPtr body A) := by
  intro newSp
  have hAmb := hoEmptyExitAmb_pcFree newSp bodyPtr typeW destPtr body A hA
  have hrest : newSp + signExtend12 (16 : BitVec 12) = sp0 := by
    simp only [se12_16]
    change (sp0 + (-16 : Word)) + (16 : Word) = sp0
    exact frame_restore sp0
  -- reshape residual post → loadSeq pre
  have hpre_load : ∀ h,
      (((.x1 ↦ᵣ (pc 20)) **
        shaCallReturn newSp Blob destPtr (hashOneBlob (typeByte typeW) [])) **
        hoShaResidualF newSp raVal bodyPtr typeW (0 : Word) destPtr body A) h →
      (hoEpiLoadPre newSp raVal bodyPtr typeW destPtr body A) h := by
    intro h hp
    dsimp only [shaCallReturn, hoShaResidualF, hoEpiLoadPre, hoEmptyExitAmb,
      regsAt_hoFrame] at hp ⊢
    -- regsAt_hoFrame gives x1↦raVal, but we need x1↦pc20 from residual
    -- residual has x1=pc20 already outside; rewrite regsAt for current vals
    simp only [regsAt, hoFrame, List.foldr, sepConj_emp_right'] at hp ⊢
    xperm_chunked hp
  -- loadSeq 1-slot: LD ra from frame
  have hload0 := loadSeq_spec hoFrame newSp (hoVals raVal)
    (fun | .x1 => pc 20 | _ => 0) (pc 20) (by decide) hoFrame_hne
  have hloadC := cpsTripleWithin_extend_code
    (fun a i hs => by
      have hmem := mem_at 20 (.LD .x1 .x2 (0 : BitVec 12)) (pc 20)
        hpc20 (by rw [hoProgL_len]; norm_num) (by rfl)
      simp only [loadProg, hoFrame, List.map] at hs
      exact hmem a i hs) hload0
  rw [hpc2021] at hloadC
  have hloadF := cpsTripleWithin_frameR
    (hoEmptyExitAmb newSp bodyPtr typeW destPtr body A) hAmb hloadC
  have c_load : cpsTripleWithin 1 (pc 20) (pc 21) fullCodeHo
      (hoEpiLoadPre newSp raVal bodyPtr typeW destPtr body A)
      ((.x2 ↦ᵣ newSp) ** regsAt hoFrame (hoVals raVal) **
        frameSlotsSaved hoFrame newSp (hoVals raVal) **
        hoEmptyExitAmb newSp bodyPtr typeW destPtr body A) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [hoEpiLoadPre] at hp
        xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq)
      hloadF
  -- ADDI sp, +16
  have haddi0 := addi_spec_gen_same_within .x2 newSp (16 : BitVec 12) (pc 21) (by decide)
  have haddiC := cpsTripleWithin_extend_code
    (mem_at 21 (.ADDI .x2 .x2 (16 : BitVec 12)) (pc 21)
      hpc21 (by rw [hoProgL_len]; norm_num) ho_ins21) haddi0
  rw [hpc2122] at haddiC
  have haddiF := cpsTripleWithin_frameR
    (regsAt hoFrame (hoVals raVal) **
      frameSlotsSaved hoFrame newSp (hoVals raVal) **
      hoEmptyExitAmb newSp bodyPtr typeW destPtr body A)
    (by
      exact pcFree_sepConj (pcFree_regsAt _ _)
        (pcFree_sepConj (pcFree_frameSlotsSaved _ _ _) hAmb))
    haddiC
  have c_addi : cpsTripleWithin 1 (pc 21) (pc 22) fullCodeHo
      ((.x2 ↦ᵣ newSp) ** regsAt hoFrame (hoVals raVal) **
        frameSlotsSaved hoFrame newSp (hoVals raVal) **
        hoEmptyExitAmb newSp bodyPtr typeW destPtr body A)
      ((.x2 ↦ᵣ sp0) ** regsAt hoFrame (hoVals raVal) **
        frameSlotsSaved hoFrame newSp (hoVals raVal) **
        hoEmptyExitAmb newSp bodyPtr typeW destPtr body A) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by
        change ((.x2 ↦ᵣ (newSp + signExtend12 (16 : BitVec 12))) ** _) _ at hq
        simp only [hrest] at hq
        xperm_chunked hq)
      haddiF
  -- JALR ret
  have hjalr0 := EvmAsm.Evm64.ret_spec_within' (pc 22) raVal
  rw [heven] at hjalr0
  have hjalrC := cpsTripleWithin_extend_code
    (mem_at 22 (.JALR .x0 .x1 (0 : BitVec 12)) (pc 22)
      hpc22 (by rw [hoProgL_len]; norm_num) ho_ins22) hjalr0
  have hjalrF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp0) **
      frameSlotsSaved hoFrame newSp (hoVals raVal) **
      hoEmptyExitAmb newSp bodyPtr typeW destPtr body A)
    (by
      exact pcFree_sepConj pcFree_regIs
        (pcFree_sepConj (pcFree_frameSlotsSaved _ _ _) hAmb))
    hjalrC
  have c_ret : cpsTripleWithin 1 (pc 22) raVal fullCodeHo
      ((.x2 ↦ᵣ sp0) ** regsAt hoFrame (hoVals raVal) **
        frameSlotsSaved hoFrame newSp (hoVals raVal) **
        hoEmptyExitAmb newSp bodyPtr typeW destPtr body A)
      (hoEmptyExitPost sp0 raVal bodyPtr typeW destPtr body A) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        rw [regsAt_hoFrame] at hp
        xperm_chunked hp)
      (fun _ hq => by
        dsimp only [hoEmptyExitPost]
        xperm_chunked hq)
      hjalrF
  have hall := cpsTripleWithin_seq_same_cr c_load
    (cpsTripleWithin_seq_same_cr c_addi c_ret)
  exact cpsTripleWithin_weaken hpre_load (fun _ hq => hq) hall

/-! ### General (any body length) residual call + epi -/

/-- Exit ambient for any body: digest = sha256 (type‖body). -/
def hoExitAmb (newSp bodyPtr typeW lenW destPtr : Word)
    (body : List (BitVec 8)) (A : Assertion) : Assertion :=
  stackFree newSp 6 **
  regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ lenW) ** (.x24 ↦ᵣ destPtr) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion bodyPtr body **
  bytesRegion Blob (hashOneBlob (typeByte typeW) body) **
  bytesRegion destPtr (sha256 (hashOneBlob (typeByte typeW) body)) ** A

theorem hoExitAmb_pcFree (newSp bodyPtr typeW lenW destPtr : Word)
    (body : List (BitVec 8)) (A : Assertion) (hA : A.pcFree) :
    (hoExitAmb newSp bodyPtr typeW lenW destPtr body A).pcFree := by
  simp only [hoExitAmb]
  repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_stackFree _ _
    | exact pcFree_emp
    | apply pcFree_sepConj
    | exact hA

def hoExitPost (sp0 raVal bodyPtr typeW lenW destPtr : Word)
    (body : List (BitVec 8)) (A : Assertion) : Assertion :=
  let newSp := sp0 + (-16 : Word)
  (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ sp0) **
  frameSlotsSaved hoFrame newSp (hoVals raVal) **
  hoExitAmb newSp bodyPtr typeW lenW destPtr body A

/-- Residual call for body of length `body.length`, lenW = ofNat body.length.
    Pre: after sha ABI with blob = type‖body and a1 = lenW+1.
    Fuel 1+shaResidualFuel. pc19→pc20. -/
theorem hash_one_sha_call
    (newSp raVal bodyPtr typeW lenW destPtr : Word)
    (body outOld : List (BitVec 8))
    (A : Assertion) (_hA : A.pcFree)
    ( _hlen : lenW = BitVec.ofNat 64 body.length)
    (h_sha : shaCallWithinShape fullCodeHo (pc 19) raVal newSp
        Blob (lenW + (1 : Word)) destPtr
        (hashOneBlob (typeByte typeW) body) outOld
        (jalOff GuestAddrs.zkvm_sha256 (GuestAddrs.erh_hash_one + 76))
        shaResidualFuel
        (hoShaResidualF newSp raVal bodyPtr typeW lenW destPtr body A)) :
    cpsTripleWithin (1 + shaResidualFuel) (pc 19) (pc 20) fullCodeHo
      (hoAfterShaAbi newSp raVal bodyPtr typeW lenW destPtr body
        (hashOneBlob (typeByte typeW) body) outOld A)
      (((.x1 ↦ᵣ (pc 20)) **
        shaCallReturn newSp Blob destPtr (hashOneBlob (typeByte typeW) body)) **
        hoShaResidualF newSp raVal bodyPtr typeW lenW destPtr body A) := by
  obtain ⟨_, _, _, _, _, _, hcall⟩ := h_sha
  have hpc : (pc 19 : Word) + 4 = pc 20 := hpc1920
  have hcall' : cpsTripleWithin (1 + shaResidualFuel) (pc 19) (pc 20) fullCodeHo
      (((.x1 ↦ᵣ raVal) **
        shaCallEntry newSp Blob (lenW + (1 : Word)) destPtr
          (hashOneBlob (typeByte typeW) body) outOld) **
        hoShaResidualF newSp raVal bodyPtr typeW lenW destPtr body A)
      (((.x1 ↦ᵣ (pc 20)) **
        shaCallReturn newSp Blob destPtr (hashOneBlob (typeByte typeW) body)) **
        hoShaResidualF newSp raVal bodyPtr typeW lenW destPtr body A) := by
    simpa [hpc] using hcall
  have hpre : ∀ h,
      (hoAfterShaAbi newSp raVal bodyPtr typeW lenW destPtr body
        (hashOneBlob (typeByte typeW) body) outOld A) h →
      (((.x1 ↦ᵣ raVal) **
        shaCallEntry newSp Blob (lenW + (1 : Word)) destPtr
          (hashOneBlob (typeByte typeW) body) outOld) **
        hoShaResidualF newSp raVal bodyPtr typeW lenW destPtr body A) h := by
    intro h hp
    dsimp only [hoAfterShaAbi, shaCallEntry, hoShaResidualF, hashOneBlob] at hp ⊢
    have hx5 := @regIs_implies_regOwn (r := .x5) (v := Blob)
    have hx6 := @regIs_implies_regOwn (r := .x6) (v := Blob + (1 : Word))
    have hx7 := @regIs_implies_regOwn (r := .x7) (v := bodyPtr)
    have hx28 := @regIs_implies_regOwn (r := .x28) (v := lenW)
    have hp' :
        (((.x5 ↦ᵣ Blob) ** (.x6 ↦ᵣ (Blob + (1 : Word))) **
            (.x7 ↦ᵣ bodyPtr) ** (.x28 ↦ᵣ lenW)) **
          ((.x10 ↦ᵣ Blob) ** (.x11 ↦ᵣ (lenW + (1 : Word))) ** (.x12 ↦ᵣ destPtr) **
            (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
            frameSlotsSaved hoFrame newSp (hoVals raVal) **
            stackFree newSp 6 **
            (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ lenW) **
            (.x24 ↦ᵣ destPtr) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion bodyPtr body **
            bytesRegion Blob (typeByte typeW :: body) **
            bytesRegion destPtr outOld ** A)) h := by
      xperm_chunked hp
    have hpDrop :
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28) **
          ((.x10 ↦ᵣ Blob) ** (.x11 ↦ᵣ (lenW + (1 : Word))) ** (.x12 ↦ᵣ destPtr) **
            (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
            frameSlotsSaved hoFrame newSp (hoVals raVal) **
            stackFree newSp 6 **
            (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ lenW) **
            (.x24 ↦ᵣ destPtr) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion bodyPtr body **
            bytesRegion Blob (typeByte typeW :: body) **
            bytesRegion destPtr outOld ** A)) h := by
      refine (sepConj_mono ?_ (fun _ hx => hx) _) hp'
      intro h' ht
      exact sepConj_mono hx5 (sepConj_mono hx6 (sepConj_mono hx7 hx28)) h' ht
    xperm_chunked hpDrop
  exact cpsTripleWithin_weaken hpre (fun _ hq => hq) hcall'

/-- Epi after residual for any body. Fuel 3. pc20→raVal. -/
theorem hash_one_epi
    (sp0 raVal bodyPtr typeW lenW destPtr : Word)
    (body : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (heven : (raVal &&& ~~~(1 : Word)) = raVal) :
    let newSp := sp0 + (-16 : Word)
    cpsTripleWithin 3 (pc 20) raVal fullCodeHo
      (((.x1 ↦ᵣ (pc 20)) **
        shaCallReturn newSp Blob destPtr (hashOneBlob (typeByte typeW) body)) **
        hoShaResidualF newSp raVal bodyPtr typeW lenW destPtr body A)
      (hoExitPost sp0 raVal bodyPtr typeW lenW destPtr body A) := by
  intro newSp
  have hAmb := hoExitAmb_pcFree newSp bodyPtr typeW lenW destPtr body A hA
  have hrest : newSp + signExtend12 (16 : BitVec 12) = sp0 := by
    simp only [se12_16]
    change (sp0 + (-16 : Word)) + (16 : Word) = sp0
    exact frame_restore sp0
  have hpre_load : ∀ h,
      (((.x1 ↦ᵣ (pc 20)) **
        shaCallReturn newSp Blob destPtr (hashOneBlob (typeByte typeW) body)) **
        hoShaResidualF newSp raVal bodyPtr typeW lenW destPtr body A) h →
      ((.x2 ↦ᵣ newSp) ** regsAt hoFrame (fun | .x1 => pc 20 | _ => 0) **
        frameSlotsSaved hoFrame newSp (hoVals raVal) **
        hoExitAmb newSp bodyPtr typeW lenW destPtr body A) h := by
    intro h hp
    dsimp only [shaCallReturn, hoShaResidualF, hoExitAmb, regsAt_hoFrame] at hp ⊢
    simp only [regsAt, hoFrame, List.foldr, sepConj_emp_right'] at hp ⊢
    xperm_chunked hp
  have hload0 := loadSeq_spec hoFrame newSp (hoVals raVal)
    (fun | .x1 => pc 20 | _ => 0) (pc 20) (by decide) hoFrame_hne
  have hloadC := cpsTripleWithin_extend_code
    (fun a i hs => by
      have hmem := mem_at 20 (.LD .x1 .x2 (0 : BitVec 12)) (pc 20)
        hpc20 (by rw [hoProgL_len]; norm_num) (by rfl)
      simp only [loadProg, hoFrame, List.map] at hs
      exact hmem a i hs) hload0
  rw [hpc2021] at hloadC
  have hloadF := cpsTripleWithin_frameR
    (hoExitAmb newSp bodyPtr typeW lenW destPtr body A) hAmb hloadC
  have c_load : cpsTripleWithin 1 (pc 20) (pc 21) fullCodeHo
      ((.x2 ↦ᵣ newSp) ** regsAt hoFrame (fun | .x1 => pc 20 | _ => 0) **
        frameSlotsSaved hoFrame newSp (hoVals raVal) **
        hoExitAmb newSp bodyPtr typeW lenW destPtr body A)
      ((.x2 ↦ᵣ newSp) ** regsAt hoFrame (hoVals raVal) **
        frameSlotsSaved hoFrame newSp (hoVals raVal) **
        hoExitAmb newSp bodyPtr typeW lenW destPtr body A) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq)
      hloadF
  have haddi0 := addi_spec_gen_same_within .x2 newSp (16 : BitVec 12) (pc 21) (by decide)
  have haddiC := cpsTripleWithin_extend_code
    (mem_at 21 (.ADDI .x2 .x2 (16 : BitVec 12)) (pc 21)
      hpc21 (by rw [hoProgL_len]; norm_num) ho_ins21) haddi0
  rw [hpc2122] at haddiC
  have haddiF := cpsTripleWithin_frameR
    (regsAt hoFrame (hoVals raVal) **
      frameSlotsSaved hoFrame newSp (hoVals raVal) **
      hoExitAmb newSp bodyPtr typeW lenW destPtr body A)
    (by
      exact pcFree_sepConj (pcFree_regsAt _ _)
        (pcFree_sepConj (pcFree_frameSlotsSaved _ _ _) hAmb))
    haddiC
  have c_addi : cpsTripleWithin 1 (pc 21) (pc 22) fullCodeHo
      ((.x2 ↦ᵣ newSp) ** regsAt hoFrame (hoVals raVal) **
        frameSlotsSaved hoFrame newSp (hoVals raVal) **
        hoExitAmb newSp bodyPtr typeW lenW destPtr body A)
      ((.x2 ↦ᵣ sp0) ** regsAt hoFrame (hoVals raVal) **
        frameSlotsSaved hoFrame newSp (hoVals raVal) **
        hoExitAmb newSp bodyPtr typeW lenW destPtr body A) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by
        change ((.x2 ↦ᵣ (newSp + signExtend12 (16 : BitVec 12))) ** _) _ at hq
        simp only [hrest] at hq
        xperm_chunked hq)
      haddiF
  have hjalr0 := EvmAsm.Evm64.ret_spec_within' (pc 22) raVal
  rw [heven] at hjalr0
  have hjalrC := cpsTripleWithin_extend_code
    (mem_at 22 (.JALR .x0 .x1 (0 : BitVec 12)) (pc 22)
      hpc22 (by rw [hoProgL_len]; norm_num) ho_ins22) hjalr0
  have hjalrF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp0) **
      frameSlotsSaved hoFrame newSp (hoVals raVal) **
      hoExitAmb newSp bodyPtr typeW lenW destPtr body A)
    (by
      exact pcFree_sepConj pcFree_regIs
        (pcFree_sepConj (pcFree_frameSlotsSaved _ _ _) hAmb))
    hjalrC
  have c_ret : cpsTripleWithin 1 (pc 22) raVal fullCodeHo
      ((.x2 ↦ᵣ sp0) ** regsAt hoFrame (hoVals raVal) **
        frameSlotsSaved hoFrame newSp (hoVals raVal) **
        hoExitAmb newSp bodyPtr typeW lenW destPtr body A)
      (hoExitPost sp0 raVal bodyPtr typeW lenW destPtr body A) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        rw [regsAt_hoFrame] at hp
        xperm_chunked hp)
      (fun _ hq => by
        dsimp only [hoExitPost]
        xperm_chunked hq)
      hjalrF
  have hall := cpsTripleWithin_seq_same_cr c_load
    (cpsTripleWithin_seq_same_cr c_addi c_ret)
  exact cpsTripleWithin_weaken hpre_load (fun _ hq => hq) hall

end EvmAsm.Codegen.ExecutionRequestsHashHashOneShaAbi
