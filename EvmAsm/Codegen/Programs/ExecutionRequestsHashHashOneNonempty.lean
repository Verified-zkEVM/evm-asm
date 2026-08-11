/-
  ExecutionRequestsHashHashOneNonempty — nonempty body path under residual h_sha.

  Path after la+SB type: copy setup → copy loop (BEQ ntaken first) →
  sha ABI from post-copy ambient → residual → epi.

  Domain: body ≠ [], bodyPtr%8=0, blob0 = typeByte :: body (scratch prefilled),
  lenW = ofNat body.length < 2^64.
  Residual h_sha = UNPROVEN-CALLEE DEPENDENCY (#12018 owns discharge).
  Parent: #12011 option B.
-/
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Programs.ExecutionRequestsHashShaResidual
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOne
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneBody
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneLa
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneEmpty
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneCopy
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneShaAbi
import EvmAsm.Stateless.SpecRef.Crypto

namespace EvmAsm.Codegen.ExecutionRequestsHashHashOneNonempty

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.ExecutionRequestsHashShaResidual
open EvmAsm.Codegen.ExecutionRequestsHashHashOne
open EvmAsm.Codegen.ExecutionRequestsHashHashOneBody
open EvmAsm.Codegen.ExecutionRequestsHashHashOneLa
open EvmAsm.Codegen.ExecutionRequestsHashHashOneEmpty
open EvmAsm.Codegen.ExecutionRequestsHashHashOneCopy
open EvmAsm.Codegen.ExecutionRequestsHashHashOneShaAbi
open EvmAsm.Stateless.SpecRef
open List

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
private theorem hpc1516 : (pc 15 : Word) + 4 = pc 16 := by simp only [pc]; decide
private theorem hpc1517 : (pc 15 : Word) + 8 = pc 17 := by simp only [pc]; decide
private theorem hpc1718 : (pc 17 : Word) + 4 = pc 18 := by simp only [pc]; decide
private theorem hpc1819 : (pc 18 : Word) + 4 = pc 19 := by simp only [pc]; decide

private theorem la_blob_hi60 :
    laHi GuestAddrs.erh_blob (GuestAddrs.erh_hash_one + 60) =
      Rv64.laHi (pc 15) Blob := by simp only [pc]; decide
private theorem la_blob_lo60 :
    laLo GuestAddrs.erh_blob (GuestAddrs.erh_hash_one + 60) =
      Rv64.laLo (pc 15) Blob := by simp only [pc]; decide
private theorem la_blob_range60 : laInRange (pc 15) Blob := by
  simp only [pc]; decide

private theorem se12_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide

private theorem ofNat_ne_zero (n : Nat) (hn : n ≠ 0) (hbound : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ (0 : Word) := by
  intro heq
  have := congrArg BitVec.toNat heq
  have hmod : (BitVec.ofNat 64 n).toNat = n := by
    simp only [BitVec.toNat_ofNat]; omega
  have hz : (0 : Word).toNat = 0 := rfl
  omega

/-! ### Pure: copy into already-final blob is identity -/

theorem set_get_self (l : List (BitVec 8)) (i : Nat) (h : i < l.length) :
    l.set i (l[i]'h) = l := by
  induction l generalizing i with
  | nil => cases h
  | cons x xs ih =>
    cases i with
    | zero => simp [List.set]
    | succ j =>
      simp only [List.set, List.getElem_cons_succ]
      congr 1
      exact ih j (Nat.lt_of_succ_lt_succ h)

theorem copyBlob_noop (body seed : List (BitVec 8)) (done k : Nat)
    (hfit : done + k ≤ body.length)
    (hseed : seed.length ≥ 1 + body.length)
    (hagree : ∀ (i : Nat) (_hi : i < k)
        (hs : 1 + (done + i) < seed.length)
        (hb : done + i < body.length),
      seed[1 + (done + i)]'hs = body[done + i]'hb) :
    copyBlob body seed done k = seed := by
  revert hfit hagree
  induction k with
  | zero => intro _ _; rfl
  | succ k ih =>
    intro hfit hagree
    have hlt : done + k < body.length := by omega
    rw [copyBlob_succ body seed done k hlt]
    have ih' : copyBlob body seed done k = seed := by
      apply ih
      · omega
      · intro i hi hs hb; exact hagree i (by omega) hs hb
    rw [ih']
    have hidx : 1 + (done + k) < seed.length := by omega
    have heq : body[done + k]'hlt = seed[1 + (done + k)]'hidx :=
      (hagree k (by omega) hidx hlt).symm
    rw [heq]
    exact set_get_self seed (1 + (done + k)) hidx

theorem copyBlob_id (t : BitVec 8) (body : List (BitVec 8)) :
    copyBlob body (t :: body) 0 body.length = t :: body := by
  apply copyBlob_noop
  · omega
  · simp; omega
  · intro i hi hs hb
    simp only [Nat.zero_add] at hs hb ⊢
    have hlt : 1 + i < (t :: body).length := by simp; omega
    set_option linter.unnecessarySimpa false in
    exact (by simpa [Nat.add_comm 1 i] using List.getElem_cons_succ t body i hlt)

theorem copyBlob_hashOne (typeW : Word) (body : List (BitVec 8)) :
    copyBlob body (hashOneBlob (typeByte typeW) body) 0 body.length =
      hashOneBlob (typeByte typeW) body := by
  simp only [hashOneBlob]
  exact copyBlob_id (typeByte typeW) body

/-! ### Post-copy ambient (advanced cursors as owns) -/

/-- After full copy: blob = type‖body; cursors advanced; x28=0; owns x6/x7/x29. -/
def hoAfterCopyDone (newSp raVal bodyPtr typeW lenW destPtr : Word)
    (body outBytes : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
  frameSlotsSaved hoFrame newSp (hoVals raVal) **
  stackFree newSp 6 **
  (.x5 ↦ᵣ Blob) **
  regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ lenW) ** (.x24 ↦ᵣ destPtr) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion bodyPtr body **
  bytesRegion Blob (hashOneBlob (typeByte typeW) body) **
  bytesRegion destPtr outBytes ** A

theorem hoAfterCopyDone_pcFree
    (newSp raVal bodyPtr typeW lenW destPtr : Word)
    (body outBytes : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree) :
    (hoAfterCopyDone newSp raVal bodyPtr typeW lenW destPtr body outBytes A).pcFree := by
  simp only [hoAfterCopyDone]; pcf; exact hA

/-- Reshape copy-loop Done → hoAfterCopyDone (peel advanced regs to owns). -/
theorem copy_done_to_after
    (newSp raVal bodyPtr typeW destPtr : Word)
    (body outBytes : List (BitVec 8))
    (A : Assertion) (_hA : A.pcFree)
    (n : Nat) (_hn : n = body.length)
    (_hbound : n < 2 ^ 64) :
    ∀ h,
      (hoCopyDone bodyPtr body (hashOneBlob (typeByte typeW) body) n
        (hoCopyF newSp raVal bodyPtr typeW (BitVec.ofNat 64 n) destPtr
          outBytes (stackFree newSp 6 ** A))) h →
      (hoAfterCopyDone newSp raVal bodyPtr typeW (BitVec.ofNat 64 n) destPtr
        body outBytes A) h := by
  intro h hp
  dsimp only [hoCopyDone, hoCopyF, hoAfterCopyDone, hashOneBlob] at hp ⊢
  have hx6 := @regIs_implies_regOwn (r := .x6)
    (v := Blob + BitVec.ofNat 64 (1 + n))
  have hx7 := @regIs_implies_regOwn (r := .x7)
    (v := bodyPtr + BitVec.ofNat 64 n)
  have hx28 := @regIs_implies_regOwn (r := .x28) (v := (0 : Word))
  -- front advanced regs then drop to owns
  have hp' :
      (((.x6 ↦ᵣ (Blob + BitVec.ofNat 64 (1 + n))) **
          (.x7 ↦ᵣ (bodyPtr + BitVec.ofNat 64 n)) **
          (.x28 ↦ᵣ (0 : Word)) ** regOwn .x29) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
          frameSlotsSaved hoFrame newSp (hoVals raVal) **
          stackFree newSp 6 **
          (.x5 ↦ᵣ Blob) **
          (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) **
          (.x26 ↦ᵣ BitVec.ofNat 64 n) ** (.x24 ↦ᵣ destPtr) **
          (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion bodyPtr body **
          bytesRegion Blob (typeByte typeW :: body) **
          bytesRegion destPtr outBytes ** A)) h := by
    xperm_chunked hp
  have hpDrop :
      ((regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29) **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
          frameSlotsSaved hoFrame newSp (hoVals raVal) **
          stackFree newSp 6 **
          (.x5 ↦ᵣ Blob) **
          (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) **
          (.x26 ↦ᵣ BitVec.ofNat 64 n) ** (.x24 ↦ᵣ destPtr) **
          (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion bodyPtr body **
          bytesRegion Blob (typeByte typeW :: body) **
          bytesRegion destPtr outBytes ** A)) h := by
    refine (sepConj_mono ?_ (fun _ hx => hx) _) hp'
    intro h' ht
    exact sepConj_mono hx6 (sepConj_mono hx7 (sepConj_mono hx28 (fun _ hx => hx))) h' ht
  xperm_chunked hpDrop

/-- Setup at pc8 → inv for full copy. -/
theorem setup_to_copy_inv
    (newSp raVal bodyPtr typeW destPtr : Word)
    (body outBytes : List (BitVec 8))
    (A : Assertion) (_hA : A.pcFree)
    (n : Nat) (_hn : n = body.length) (_hne : n ≠ 0) (_hbound : n < 2 ^ 64)
    (v29 : Word) :
    ∀ h,
      ((.x29 ↦ᵣ v29) **
        hoAfterCopySetupSf newSp raVal bodyPtr typeW (BitVec.ofNat 64 n) destPtr
          body body outBytes A) h →
      (hoCopyInv bodyPtr body (hashOneBlob (typeByte typeW) body) n 0
        (hoCopyF newSp raVal bodyPtr typeW (BitVec.ofNat 64 n) destPtr
          outBytes (stackFree newSp 6 ** A))) h := by
  intro h hp
  dsimp only [hoAfterCopySetupSf, hoAfterCopySetup, hoCopyInv, hoCopyF,
    hashOneBlob] at hp ⊢
  -- x6 = Blob+1 = Blob+ofNat(1+0); x7 = bodyPtr = bodyPtr+ofNat 0; x28 = ofNat n
  have hx6 : Blob + BitVec.ofNat 64 (1 + 0) = Blob + (1 : Word) := by
    apply congrArg; decide
  have hx7 : bodyPtr + BitVec.ofNat 64 0 = bodyPtr := by
    change bodyPtr + (0 : Word) = bodyPtr
    exact BitVec.add_zero bodyPtr
  have hx29 := @regIs_implies_regOwn (r := .x29) (v := v29)
  -- Flatten setup (Blob+1 / bodyPtr), drop x29, then rewrite into inv ofNat form
  have hp0 :
      ((.x29 ↦ᵣ v29) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
        frameSlotsSaved hoFrame newSp (hoVals raVal) **
        stackFree newSp 6 **
        (.x5 ↦ᵣ Blob) **
        (.x6 ↦ᵣ (Blob + (1 : Word))) **
        (.x7 ↦ᵣ bodyPtr) **
        (.x28 ↦ᵣ BitVec.ofNat 64 n) **
        (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) **
        (.x26 ↦ᵣ BitVec.ofNat 64 n) ** (.x24 ↦ᵣ destPtr) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion bodyPtr body **
        bytesRegion Blob (typeByte typeW :: body) **
        bytesRegion destPtr outBytes ** A) h := by
    xperm_chunked hp
  have hp1 :
      ((regOwn .x29) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
        frameSlotsSaved hoFrame newSp (hoVals raVal) **
        stackFree newSp 6 **
        (.x5 ↦ᵣ Blob) **
        (.x6 ↦ᵣ (Blob + (1 : Word))) **
        (.x7 ↦ᵣ bodyPtr) **
        (.x28 ↦ᵣ BitVec.ofNat 64 n) **
        (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) **
        (.x26 ↦ᵣ BitVec.ofNat 64 n) ** (.x24 ↦ᵣ destPtr) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion bodyPtr body **
        bytesRegion Blob (typeByte typeW :: body) **
        bytesRegion destPtr outBytes ** A) h := by
    refine (sepConj_mono hx29 (fun _ hx => hx) _) hp0
  -- Rewrite cursor equalities into ofNat form expected by hoCopyInv
  have hp2 :
      ((regOwn .x29) **
        (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
        frameSlotsSaved hoFrame newSp (hoVals raVal) **
        stackFree newSp 6 **
        (.x5 ↦ᵣ Blob) **
        (.x6 ↦ᵣ (Blob + BitVec.ofNat 64 (1 + 0))) **
        (.x7 ↦ᵣ (bodyPtr + BitVec.ofNat 64 0)) **
        (.x28 ↦ᵣ BitVec.ofNat 64 n) **
        (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) **
        (.x26 ↦ᵣ BitVec.ofNat 64 n) ** (.x24 ↦ᵣ destPtr) **
        (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion bodyPtr body **
        bytesRegion Blob (typeByte typeW :: body) **
        bytesRegion destPtr outBytes ** A) h := by
    rw [hx6, hx7]; exact hp1
  xperm_chunked hp2

/-- After sha ABI with owns for advanced cursors (post-copy). -/
def hoAfterShaAbiOwns (newSp raVal bodyPtr typeW lenW destPtr : Word)
    (body outBytes : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x10 ↦ᵣ Blob) ** (.x11 ↦ᵣ (lenW + (1 : Word))) ** (.x12 ↦ᵣ destPtr) **
  (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
  frameSlotsSaved hoFrame newSp (hoVals raVal) **
  stackFree newSp 6 **
  (.x5 ↦ᵣ Blob) **
  regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ lenW) ** (.x24 ↦ᵣ destPtr) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion bodyPtr body **
  bytesRegion Blob (hashOneBlob (typeByte typeW) body) **
  bytesRegion destPtr outBytes ** A

/-- Sha ABI from post-copy ambient. Fuel 4. pc15→pc19. -/
theorem hash_one_sha_abi_done
    (newSp raVal bodyPtr typeW lenW destPtr v10old v11old v12old : Word)
    (body outBytes : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 4 (pc 15) (pc 19) fullCodeHo
      ((.x10 ↦ᵣ v10old) ** (.x11 ↦ᵣ v11old) ** (.x12 ↦ᵣ v12old) **
        hoAfterCopyDone newSp raVal bodyPtr typeW lenW destPtr body outBytes A)
      (hoAfterShaAbiOwns newSp raVal bodyPtr typeW lenW destPtr body outBytes A) := by
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
    hoAfterCopyDone newSp raVal bodyPtr typeW lenW destPtr body outBytes A
  have hFla : Fla.pcFree := by
    dsimp only [Fla, hoAfterCopyDone]; pcf; exact hA
  have hlaF := cpsTripleWithin_frameR Fla hFla hla
  have c_la : cpsTripleWithin 2 (pc 15) (pc 17) fullCodeHo
      ((.x10 ↦ᵣ v10old) ** (.x11 ↦ᵣ v11old) ** (.x12 ↦ᵣ v12old) **
        hoAfterCopyDone newSp raVal bodyPtr typeW lenW destPtr body outBytes A)
      ((.x10 ↦ᵣ Blob) ** (.x11 ↦ᵣ v11old) ** (.x12 ↦ᵣ v12old) **
        hoAfterCopyDone newSp raVal bodyPtr typeW lenW destPtr body outBytes A) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by dsimp only [Fla] at *; xperm_chunked hp)
      (fun _ hq => by dsimp only [Fla] at hq; xperm_chunked hq)
      hlaF
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
    (.x5 ↦ᵣ Blob) **
    regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x24 ↦ᵣ destPtr) **
    (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion bodyPtr body **
    bytesRegion Blob (hashOneBlob (typeByte typeW) body) **
    bytesRegion destPtr outBytes ** A
  have hF11 : F11.pcFree := by dsimp only [F11]; pcf; exact hA
  have haddiF := cpsTripleWithin_frameR F11 hF11 haddiC
  have c_addi : cpsTripleWithin 1 (pc 17) (pc 18) fullCodeHo
      ((.x10 ↦ᵣ Blob) ** (.x11 ↦ᵣ v11old) ** (.x12 ↦ᵣ v12old) **
        hoAfterCopyDone newSp raVal bodyPtr typeW lenW destPtr body outBytes A)
      ((.x10 ↦ᵣ Blob) ** (.x11 ↦ᵣ (lenW + (1 : Word))) ** (.x12 ↦ᵣ v12old) **
        hoAfterCopyDone newSp raVal bodyPtr typeW lenW destPtr body outBytes A) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [F11] at *
        simp only [hoAfterCopyDone] at hp ⊢
        xperm_chunked hp)
      (fun _ hq => by
        dsimp only [F11] at hq
        simp only [se12_1, hoAfterCopyDone] at hq ⊢
        xperm_chunked hq)
      haddiF
  have hmv := mv_spec_gen_within .x12 .x24 destPtr v12old (pc 18) (by decide)
  have hmvC := cpsTripleWithin_extend_code
    (mem_at 18 _ (pc 18) hpc18 (by rw [hoProgL_len]; norm_num) ho_ins18) hmv
  rw [hpc1819] at hmvC
  let F12 : Assertion :=
    (.x10 ↦ᵣ Blob) ** (.x11 ↦ᵣ (lenW + (1 : Word))) **
    (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
    frameSlotsSaved hoFrame newSp (hoVals raVal) **
    stackFree newSp 6 **
    (.x5 ↦ᵣ Blob) **
    regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    (.x13 ↦ᵣ bodyPtr) ** (.x14 ↦ᵣ typeW) ** (.x26 ↦ᵣ lenW) **
    (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion bodyPtr body **
    bytesRegion Blob (hashOneBlob (typeByte typeW) body) **
    bytesRegion destPtr outBytes ** A
  have hF12 : F12.pcFree := by dsimp only [F12]; pcf; exact hA
  have hmvF := cpsTripleWithin_frameR F12 hF12 hmvC
  have c_mv : cpsTripleWithin 1 (pc 18) (pc 19) fullCodeHo
      ((.x10 ↦ᵣ Blob) ** (.x11 ↦ᵣ (lenW + (1 : Word))) ** (.x12 ↦ᵣ v12old) **
        hoAfterCopyDone newSp raVal bodyPtr typeW lenW destPtr body outBytes A)
      (hoAfterShaAbiOwns newSp raVal bodyPtr typeW lenW destPtr body outBytes A) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [F12] at *
        simp only [hoAfterCopyDone] at hp ⊢
        xperm_chunked hp)
      (fun _ hq => by
        dsimp only [F12, hoAfterShaAbiOwns] at hq ⊢
        xperm_chunked hq)
      hmvF
  exact cpsTripleWithin_seq_same_cr c_la (cpsTripleWithin_seq_same_cr c_addi c_mv)

/-- Residual F with extra own x29 (post-copy scratch). -/
def hoShaResidualF29 (newSp raVal bodyPtr typeW lenW destPtr : Word)
    (body : List (BitVec 8)) (A : Assertion) : Assertion :=
  hoShaResidualF newSp raVal bodyPtr typeW lenW destPtr body (regOwn .x29 ** A)

/-- Residual call from owns ambient. Fuel 1+shaResidualFuel. pc19→pc20.
    `h_sha` is framed with residual F including own x29. -/
theorem hash_one_sha_call_owns
    (newSp raVal bodyPtr typeW lenW destPtr : Word)
    (body outOld : List (BitVec 8))
    (A : Assertion) (_hA : A.pcFree)
    (h_sha : shaCallWithinShape fullCodeHo (pc 19) raVal newSp
        Blob (lenW + (1 : Word)) destPtr
        (hashOneBlob (typeByte typeW) body) outOld
        (jalOff GuestAddrs.zkvm_sha256 (GuestAddrs.erh_hash_one + 76))
        shaResidualFuel
        (hoShaResidualF29 newSp raVal bodyPtr typeW lenW destPtr body A)) :
    cpsTripleWithin (1 + shaResidualFuel) (pc 19) (pc 20) fullCodeHo
      (hoAfterShaAbiOwns newSp raVal bodyPtr typeW lenW destPtr body outOld A)
      (((.x1 ↦ᵣ (pc 20)) **
        shaCallReturn newSp Blob destPtr (hashOneBlob (typeByte typeW) body)) **
        hoShaResidualF29 newSp raVal bodyPtr typeW lenW destPtr body A) := by
  obtain ⟨_, _, _, _, _, _, hcall⟩ := h_sha
  have hpc : (pc 19 : Word) + 4 = pc 20 := by simp only [pc]; decide
  have hcall' : cpsTripleWithin (1 + shaResidualFuel) (pc 19) (pc 20) fullCodeHo
      (((.x1 ↦ᵣ raVal) **
        shaCallEntry newSp Blob (lenW + (1 : Word)) destPtr
          (hashOneBlob (typeByte typeW) body) outOld) **
        hoShaResidualF29 newSp raVal bodyPtr typeW lenW destPtr body A)
      (((.x1 ↦ᵣ (pc 20)) **
        shaCallReturn newSp Blob destPtr (hashOneBlob (typeByte typeW) body)) **
        hoShaResidualF29 newSp raVal bodyPtr typeW lenW destPtr body A) := by
    simpa [hpc] using hcall
  have hpre : ∀ h,
      (hoAfterShaAbiOwns newSp raVal bodyPtr typeW lenW destPtr body outOld A) h →
      (((.x1 ↦ᵣ raVal) **
        shaCallEntry newSp Blob (lenW + (1 : Word)) destPtr
          (hashOneBlob (typeByte typeW) body) outOld) **
        hoShaResidualF29 newSp raVal bodyPtr typeW lenW destPtr body A) h := by
    intro h hp
    dsimp only [hoAfterShaAbiOwns, shaCallEntry, hoShaResidualF29, hoShaResidualF,
      hashOneBlob] at hp ⊢
    have hx5 := @regIs_implies_regOwn (r := .x5) (v := Blob)
    have hp' :
        (((.x5 ↦ᵣ Blob) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29) **
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
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29) **
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
      exact sepConj_mono hx5 (fun _ hx => hx) h' ht
    xperm_chunked hpDrop
  exact cpsTripleWithin_weaken hpre (fun _ hq => hq) hcall'

/-- Compose: setup-sf → copy loop → after-done. Fuel 1+(n*7+1) but setup already done.
    From hoAfterCopySetupSf at pc8. Fuel copyLoopFuel n. -/
theorem hash_one_copy_full
    (newSp raVal bodyPtr typeW destPtr : Word)
    (body outBytes : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (n : Nat) (hn : n = body.length) (hne : n ≠ 0) (hbound : n < 2 ^ 64)
    (hsrcAlign : bodyPtr.toNat % 8 = 0)
    (hsrcOver : bodyPtr.toNat + body.length < 2 ^ 64)
    (hdstOver : Blob.toNat + (1 + body.length) < 2 ^ 64)
    (hvalidS : ∀ i, i < body.length →
      isValidByteAccess (bodyPtr + BitVec.ofNat 64 i) = true)
    (hvalidD : ∀ i, i < body.length →
      isValidByteAccess (Blob + BitVec.ofNat 64 (1 + i)) = true)
    (v29 : Word) :
    cpsTripleWithin (copyLoopFuel n) (pc 8) (pc 15) fullCodeHo
      ((.x29 ↦ᵣ v29) **
        hoAfterCopySetupSf newSp raVal bodyPtr typeW (BitVec.ofNat 64 n) destPtr
          body body outBytes A)
      (hoAfterCopyDone newSp raVal bodyPtr typeW (BitVec.ofNat 64 n) destPtr
        body outBytes A) := by
  have hF := hoCopyF_pcFree newSp raVal bodyPtr typeW (BitVec.ofNat 64 n) destPtr
    outBytes (stackFree newSp 6 ** A) (pcFree_sepConj (pcFree_stackFree _ _) hA)
  have hloop := hash_one_copy_loop bodyPtr body
    (hashOneBlob (typeByte typeW) body) n 0
    (by omega)
    (by simp [hashOneBlob]; omega)
    hsrcAlign hsrcOver hdstOver hvalidS hvalidD
    (hoCopyF newSp raVal bodyPtr typeW (BitVec.ofNat 64 n) destPtr
      outBytes (stackFree newSp 6 ** A)) hF
  -- reshape pre setup → inv; post done → after
  have hpre := setup_to_copy_inv newSp raVal bodyPtr typeW destPtr body outBytes A hA
    n hn hne hbound v29
  have hpost := copy_done_to_after newSp raVal bodyPtr typeW destPtr body outBytes A hA
    n hn hbound
  -- after loop blob = copyBlob ... = hashOneBlob via copyBlob_hashOne
  have hblob := copyBlob_hashOne typeW body
  have hloop' :
      cpsTripleWithin (copyLoopFuel n) (pc 8) (pc 15) fullCodeHo
        (hoCopyInv bodyPtr body (hashOneBlob (typeByte typeW) body) n 0
          (hoCopyF newSp raVal bodyPtr typeW (BitVec.ofNat 64 n) destPtr
            outBytes (stackFree newSp 6 ** A)))
        (hoCopyDone bodyPtr body (hashOneBlob (typeByte typeW) body) n
          (hoCopyF newSp raVal bodyPtr typeW (BitVec.ofNat 64 n) destPtr
            outBytes (stackFree newSp 6 ** A))) := by
    subst hn
    refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hloop
    intro h hq
    -- hq : Done (copyBlob ... 0 length) (0+length)
    simpa [hblob, Nat.zero_add] using hq
  exact cpsTripleWithin_weaken hpre hpost hloop'

end EvmAsm.Codegen.ExecutionRequestsHashHashOneNonempty
