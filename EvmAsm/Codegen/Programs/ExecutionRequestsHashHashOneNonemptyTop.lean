/-
  ExecutionRequestsHashHashOneNonemptyTop — nonempty-body `erh_hash_one` under h_sha.

  Path: prologue → la+SB type → copy setup → copy loop → sha ABI → residual
  zkvm_sha256 → epi restore+ret.

  Domain: body ≠ [], bodyPtr%8=0, lenW = ofNat body.length < 2^64,
  blob scratch length ≥ 1+body.length (seed 0::body, SB overwrites type).
  Residual h_sha = UNPROVEN-CALLEE DEPENDENCY (#12018 owns discharge).
  Parent: #12011 option B.
-/
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Programs.ExecutionRequestsHashShaResidual
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOne
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneBody
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneLa
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneEmpty
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneShaAbi
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneCopy
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneNonempty
import EvmAsm.Stateless.SpecRef.Crypto

namespace EvmAsm.Codegen.ExecutionRequestsHashHashOneNonemptyTop

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.ExecutionRequestsHashShaResidual
open EvmAsm.Codegen.ExecutionRequestsHashHashOne
open EvmAsm.Codegen.ExecutionRequestsHashHashOneBody
open EvmAsm.Codegen.ExecutionRequestsHashHashOneLa
open EvmAsm.Codegen.ExecutionRequestsHashHashOneEmpty
open EvmAsm.Codegen.ExecutionRequestsHashHashOneShaAbi
open EvmAsm.Codegen.ExecutionRequestsHashHashOneCopy
open EvmAsm.Codegen.ExecutionRequestsHashHashOneNonempty
open EvmAsm.Stateless.SpecRef

set_option maxRecDepth 8000

/-- Nonempty fuel: 2 prolog + 3 la/sb + 3 copy setup + (n*7+1) copy +
    4 sha ABI + (1+sha) + 3 epi. -/
def hashOneNonemptyFuel (n : Nat) : Nat :=
  2 + 3 + 3 + copyLoopFuel n + 4 + (1 + shaResidualFuel) + 3

theorem hashOneNonemptyFuel_eq (n : Nat) :
    hashOneNonemptyFuel n = 17 + 7 * n + shaResidualFuel := by
  simp only [hashOneNonemptyFuel, copyLoopFuel]; omega

/-- Entry temps for nonempty path (includes x29 for LBU dest). -/
def hoEntryTempsNE : Assertion :=
  (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
  (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
  (.x28 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ (0 : Word))

theorem hoEntryTempsNE_pcFree : hoEntryTempsNE.pcFree := by
  simp only [hoEntryTempsNE]
  repeat' first
    | exact pcFree_regIs
    | apply pcFree_sepConj

/-- Entry with stackFree; blob seed = 0 :: body (SB writes type at [0]). -/
def hoEntryPreNE (sp0 raVal bodyPtr typeW destPtr : Word)
    (body outBytes : List (BitVec 8)) (A : Assertion) : Assertion :=
  let newSp := sp0 + (-16 : Word)
  let nW := BitVec.ofNat 64 body.length
  hoEntryPre sp0 raVal bodyPtr typeW nW destPtr body ((0 : BitVec 8) :: body) outBytes
    (stackFree newSp 6 ** A)

/-- Exit post with own x29 residual ambient (post-copy scratch). -/
def hoExitPostNE (sp0 raVal bodyPtr typeW destPtr : Word)
    (body : List (BitVec 8)) (A : Assertion) : Assertion :=
  let nW := BitVec.ofNat 64 body.length
  hoExitPost sp0 raVal bodyPtr typeW nW destPtr body (regOwn .x29 ** A)

/-- Nonempty-body top under residual `h_sha`.
    Pre: body ≠ [], bodyPtr aligned, blob seed 0::body, out length 32,
    stack free 6 below newSp, ra even.
    Post: digest = sha256 (type‖body), sp/ra restored. -/
theorem erh_hash_one_spec_within_nonempty
    (sp0 raVal bodyPtr typeW destPtr : Word)
    (body outOld : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (heven : (raVal &&& ~~~(1 : Word)) = raVal)
    (_hout : outOld.length = 32)
    (hne : body ≠ [])
    (hsrcAlign : bodyPtr.toNat % 8 = 0)
    (hsrcOver : bodyPtr.toNat + body.length < 2 ^ 64)
    (hdstOver : Blob.toNat + (1 + body.length) < 2 ^ 64)
    (hbound : body.length < 2 ^ 64)
    (hvalidS : ∀ i, i < body.length →
      isValidByteAccess (bodyPtr + BitVec.ofNat 64 i) = true)
    (hvalidD : ∀ i, i < body.length →
      isValidByteAccess (Blob + BitVec.ofNat 64 (1 + i)) = true)
    (h_sha : shaCallWithinShape fullCodeHo (pc 19) raVal (sp0 + (-16 : Word))
        Blob (BitVec.ofNat 64 body.length + (1 : Word)) destPtr
        (hashOneBlob (typeByte typeW) body) outOld
        (jalOff GuestAddrs.zkvm_sha256 (GuestAddrs.erh_hash_one + 76))
        shaResidualFuel
        (hoShaResidualF29 (sp0 + (-16 : Word)) raVal bodyPtr typeW
          (BitVec.ofNat 64 body.length) destPtr body A)) :
    cpsTripleWithin (hashOneNonemptyFuel body.length) (pc 0) raVal fullCodeHo
      (hoEntryTempsNE ** hoEntryPreNE sp0 raVal bodyPtr typeW destPtr body outOld A)
      (hoExitPostNE sp0 raVal bodyPtr typeW destPtr body A) := by
  set newSp := sp0 + (-16 : Word)
  set n := body.length
  set nW := BitVec.ofNat 64 n
  have hn : n = body.length := rfl
  have hneN : n ≠ 0 := by
    intro hz; apply hne; exact List.eq_nil_of_length_eq_zero hz
  have hSf : (stackFree newSp 6 ** A).pcFree :=
    pcFree_sepConj (pcFree_stackFree _ _) hA
  have hA29 : (regOwn .x29 ** A).pcFree := pcFree_sepConj pcFree_regOwn hA
  -- pieces
  have hpro := hash_one_prologue sp0 raVal bodyPtr typeW nW destPtr
    body ((0 : BitVec 8) :: body) outOld (stackFree newSp 6 ** A) hSf
  have hla := hash_one_la_sb_type newSp raVal bodyPtr typeW nW destPtr
    (0 : Word) body body outOld (0 : BitVec 8) (stackFree newSp 6 ** A) hSf
  have hsetup := hash_one_copy_setup newSp raVal bodyPtr typeW nW destPtr
    (0 : Word) (0 : Word) (0 : Word) body body outOld (stackFree newSp 6 ** A) hSf
  have hcopy := hash_one_copy_full newSp raVal bodyPtr typeW destPtr
    body outOld A hA n hn hneN hbound hsrcAlign hsrcOver hdstOver hvalidS hvalidD
    (0 : Word)
  have habi := hash_one_sha_abi_done newSp raVal bodyPtr typeW nW destPtr
    (0 : Word) (0 : Word) (0 : Word) body outOld A hA
  have hcall := hash_one_sha_call_owns newSp raVal bodyPtr typeW nW destPtr
    body outOld A hA h_sha
  have hepi := hash_one_epi sp0 raVal bodyPtr typeW nW destPtr body
    (regOwn .x29 ** A) hA29 heven
  -- prologue framed by temps
  have hproF := cpsTripleWithin_frameR hoEntryTempsNE hoEntryTempsNE_pcFree hpro
  have c0 : cpsTripleWithin 2 (pc 0) (pc 2) fullCodeHo
      (hoEntryTempsNE ** hoEntryPreNE sp0 raVal bodyPtr typeW destPtr body outOld A)
      (hoEntryTempsNE ** hoAfterPrologue newSp raVal bodyPtr typeW nW destPtr
        body ((0 : BitVec 8) :: body) outOld (stackFree newSp 6 ** A)) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [hoEntryPreNE, nW, n] at hp
        xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq)
      hproF
  -- la: focus x5 from temps
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (0 : Word)) **
      (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x29 ↦ᵣ (0 : Word)))
    (by
      repeat' first
        | exact pcFree_regIs
        | apply pcFree_sepConj)
    hla
  have c1 : cpsTripleWithin 3 (pc 2) (pc 5) fullCodeHo
      (hoEntryTempsNE ** hoAfterPrologue newSp raVal bodyPtr typeW nW destPtr
        body ((0 : BitVec 8) :: body) outOld (stackFree newSp 6 ** A))
      ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x29 ↦ᵣ (0 : Word)) **
        hoAfterType newSp raVal bodyPtr typeW nW destPtr
          body body outOld (stackFree newSp 6 ** A)) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [hoEntryTempsNE] at hp
        xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq)
      hlaF
  -- copy setup: focus x6/x7/x28; frame x10-12 + x29
  have hsetupF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x29 ↦ᵣ (0 : Word)))
    (by
      exact pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs pcFree_regIs)))
    hsetup
  have c2 : cpsTripleWithin 3 (pc 5) (pc 8) fullCodeHo
      ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x29 ↦ᵣ (0 : Word)) **
        hoAfterType newSp raVal bodyPtr typeW nW destPtr
          body body outOld (stackFree newSp 6 ** A))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x29 ↦ᵣ (0 : Word)) **
        hoAfterCopySetup newSp raVal bodyPtr typeW nW destPtr
          body body outOld (stackFree newSp 6 ** A)) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq)
      hsetupF
  -- copy full: reshape to Sf + x29; post after-done; frame ABI temps x10-12
  have hcopyF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)))
    (by
      exact pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs pcFree_regIs))
    hcopy
  have c3 : cpsTripleWithin (copyLoopFuel n) (pc 8) (pc 15) fullCodeHo
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x29 ↦ᵣ (0 : Word)) **
        hoAfterCopySetup newSp raVal bodyPtr typeW nW destPtr
          body body outOld (stackFree newSp 6 ** A))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        hoAfterCopyDone newSp raVal bodyPtr typeW nW destPtr body outOld A) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [hoAfterCopySetupSf, nW, n] at hcopyF hp ⊢
        xperm_chunked hp)
      (fun _ hq => by
        dsimp only [nW, n] at hq ⊢
        xperm_chunked hq)
      hcopyF
  -- sha ABI framed by nothing extra (temps in focus)
  have c4 : cpsTripleWithin 4 (pc 15) (pc 19) fullCodeHo
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        hoAfterCopyDone newSp raVal bodyPtr typeW nW destPtr body outOld A)
      (hoAfterShaAbiOwns newSp raVal bodyPtr typeW nW destPtr body outOld A) := by
    dsimp only [nW, n] at habi ⊢
    exact habi
  -- residual + epi
  have c5 : cpsTripleWithin (1 + shaResidualFuel) (pc 19) (pc 20) fullCodeHo
      (hoAfterShaAbiOwns newSp raVal bodyPtr typeW nW destPtr body outOld A)
      (((.x1 ↦ᵣ (pc 20)) **
        shaCallReturn newSp Blob destPtr (hashOneBlob (typeByte typeW) body)) **
        hoShaResidualF29 newSp raVal bodyPtr typeW nW destPtr body A) := by
    dsimp only [nW, n] at hcall ⊢
    exact hcall
  have c6 : cpsTripleWithin 3 (pc 20) raVal fullCodeHo
      (((.x1 ↦ᵣ (pc 20)) **
        shaCallReturn newSp Blob destPtr (hashOneBlob (typeByte typeW) body)) **
        hoShaResidualF29 newSp raVal bodyPtr typeW nW destPtr body A)
      (hoExitPostNE sp0 raVal bodyPtr typeW destPtr body A) := by
    -- F29 = F (own x29 ** A); epi wants F (own x29 ** A)
    dsimp only [hoShaResidualF29, hoExitPostNE, nW, n] at hepi ⊢
    exact hepi
  have c56 := cpsTripleWithin_seq_same_cr c5 c6
  have hall := cpsTripleWithin_seq_same_cr c0
    (cpsTripleWithin_seq_same_cr c1
      (cpsTripleWithin_seq_same_cr c2
        (cpsTripleWithin_seq_same_cr c3
          (cpsTripleWithin_seq_same_cr c4 c56))))
  have hfuel :
      2 + (3 + (3 + (copyLoopFuel n + (4 + (1 + shaResidualFuel + 3))))) =
        hashOneNonemptyFuel n := by
    simp only [hashOneNonemptyFuel]; omega
  simpa [hfuel, n] using hall

end EvmAsm.Codegen.ExecutionRequestsHashHashOneNonemptyTop
