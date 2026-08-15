/-
  ExecutionRequestsHashHashOneNonemptyTop — nonempty-body `erh_hash_one`
  with discharged sha256 (no residual `h_sha`).

  Path: prologue → la+SB type → copy setup → copy loop → sha ABI →
  zkvm_sha256 (via `zkvm_sha256_spec_within`) → epi restore+ret.

  Domain: body ≠ [], bodyPtr%8=0, lenW = ofNat body.length < 2^64,
  blob scratch length ≥ 1+body.length (seed 0::body, SB overwrites type),
  plus `body.length + 1 = 64*N + rem` and `ShaDischargeHyps`.
  Parent: #12011 option B. Owner #12018.
-/
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Programs.ExecutionRequestsHashShaResidual
import EvmAsm.Codegen.Programs.ExecutionRequestsHashShaDischarge
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOne
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneBody
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneLa
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneEmpty
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneShaAbi
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneCopy
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneNonempty
import EvmAsm.Codegen.Proofs.HashBridgeSha256Top
import EvmAsm.Stateless.SpecRef.Crypto

namespace EvmAsm.Codegen.ExecutionRequestsHashHashOneNonemptyTop

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.ExecutionRequestsHashShaResidual
open EvmAsm.Codegen.ExecutionRequestsHashShaDischarge
open EvmAsm.Codegen.ExecutionRequestsHashHashOne
open EvmAsm.Codegen.ExecutionRequestsHashHashOneBody
open EvmAsm.Codegen.ExecutionRequestsHashHashOneLa
open EvmAsm.Codegen.ExecutionRequestsHashHashOneEmpty
open EvmAsm.Codegen.ExecutionRequestsHashHashOneShaAbi
open EvmAsm.Codegen.ExecutionRequestsHashHashOneCopy
open EvmAsm.Codegen.ExecutionRequestsHashHashOneNonempty
open EvmAsm.Codegen.Proofs
open EvmAsm.Stateless.SpecRef

set_option maxRecDepth 8000

/-- Nonempty fuel: 2 prolog + 3 la/sb + 3 copy setup + (n*7+1) copy +
    4 sha ABI + (1+nSha) + 3 epi. -/
def hashOneNonemptyFuel (n N rem : Nat) : Nat :=
  2 + 3 + 3 + copyLoopFuel n + 4 + (1 + nSha256 N rem) + 3

theorem hashOneNonemptyFuel_eq (n N rem : Nat) :
    hashOneNonemptyFuel n N rem = 17 + 7 * n + nSha256 N rem := by
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

/-- Callee ambient for nonempty: regsAt + BSS + x30 (x29 arrives via copy path). -/
@[irreducible] def hoShaCalleeAmbNE (vals : Reg → Word)
    (st0 scratch0 iv params : List (BitVec 8)) : Assertion :=
  let ShaSt : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_state
  let ShaIvA : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_iv
  let ShaIn : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_input
  let ShaPar : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_params
  regsAt sha256Frame vals **
    bytesRegion ShaSt st0 ** bytesRegion ShaIvA iv **
    bytesRegion ShaIn scratch0 ** bytesRegion ShaPar params **
    regOwn .x30

theorem hoShaCalleeAmbNE_pcFree (vals : Reg → Word)
    (st0 scratch0 iv params : List (BitVec 8)) :
    (hoShaCalleeAmbNE vals st0 scratch0 iv params).pcFree := by
  simp only [hoShaCalleeAmbNE]
  exact pcFree_sepConj (pcFree_regsAt _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) <|
        pcFree_sepConj (bytesRegion_pcFree _ _) <|
          pcFree_sepConj (bytesRegion_pcFree _ _) pcFree_regOwn

/-- Exit leftovers: frame regs + BSS finals + x30. -/
@[irreducible] def hoShaExitLeftoversNE (vals : Reg → Word)
    (input params iv : List (BitVec 8)) (N rem : Nat) : Assertion :=
  regsAt sha256Frame vals **
    shaBssPost input params iv N rem **
    regOwn .x30

theorem hoShaExitLeftoversNE_pcFree (vals : Reg → Word)
    (input params iv : List (BitVec 8)) (N rem : Nat) :
    (hoShaExitLeftoversNE vals input params iv N rem).pcFree := by
  simp only [hoShaExitLeftoversNE]
  exact pcFree_sepConj (pcFree_regsAt _ _) <|
    pcFree_sepConj (shaBssPost_pcFree _ _ _ _ _) pcFree_regOwn

/-- Nonempty-body top discharged via `zkvm_sha256_spec_within` (no residual `h_sha`). -/
theorem erh_hash_one_spec_within_nonempty
    (sp0 raVal bodyPtr typeW destPtr : Word)
    (body outOld : List (BitVec 8)) (N rem : Nat)
    (v8 v9 v18 v19 v20 v21 : Word)
    (st0 scratch0 iv params : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (heven : (raVal &&& ~~~(1 : Word)) = raVal)
    (hout : outOld.length = 32)
    (hne : body ≠ [])
    (hsrcAlign : bodyPtr.toNat % 8 = 0)
    (hsrcOver : bodyPtr.toNat + body.length < 2 ^ 64)
    (hdstOver : Blob.toNat + (1 + body.length) < 2 ^ 64)
    (hbound : body.length < 2 ^ 64)
    (hvalidS : ∀ i, i < body.length →
      isValidByteAccess (bodyPtr + BitVec.ofNat 64 i) = true)
    (hvalidD : ∀ i, i < body.length →
      isValidByteAccess (Blob + BitVec.ofNat 64 (1 + i)) = true)
    (hpart : body.length + 1 = 64 * N + rem)
    (hyps : ShaDischargeHyps Blob destPtr (hashOneBlob (typeByte typeW) body)
        N rem st0 scratch0 iv params) :
    let vals := sha256EntryVals v8 v9 v18 v19 v20 v21
    let input := hashOneBlob (typeByte typeW) body
    cpsTripleWithin (hashOneNonemptyFuel body.length N rem) (pc 0) raVal fullCodeHo
      (hoEntryTempsNE ** hoEntryPreNE sp0 raVal bodyPtr typeW destPtr body outOld A **
        hoShaCalleeAmbNE vals st0 scratch0 iv params)
      (hoExitPostNE sp0 raVal bodyPtr typeW destPtr body A **
        hoShaExitLeftoversNE vals input params iv N rem) := by
  intro vals input
  set newSp := sp0 + (-16 : Word)
  set n := body.length
  set nW := BitVec.ofNat 64 n
  have hn : n = body.length := rfl
  have hneN : n ≠ 0 := by
    intro hz; apply hne; exact List.eq_nil_of_length_eq_zero hz
  have hSf : (stackFree newSp 6 ** A).pcFree :=
    pcFree_sepConj (pcFree_stackFree _ _) hA
  have hA29 : (regOwn .x29 ** A).pcFree := pcFree_sepConj pcFree_regOwn hA
  have hAmb := hoShaCalleeAmbNE_pcFree vals st0 scratch0 iv params
  have hLeft := hoShaExitLeftoversNE_pcFree vals input params iv N rem
  have hlenW : nW = BitVec.ofNat 64 body.length := by simp only [nW, n]
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
    body outOld N rem v8 v9 v18 v19 v20 v21 st0 scratch0 iv params A hA
    hyps hlenW hout hpart
  have hepi := hash_one_epi sp0 raVal bodyPtr typeW nW destPtr body
    (regOwn .x29 ** A) hA29 heven
  -- prologue framed by temps + callee ambient
  have hproF := cpsTripleWithin_frameR
    (hoEntryTempsNE ** hoShaCalleeAmbNE vals st0 scratch0 iv params)
    (pcFree_sepConj hoEntryTempsNE_pcFree hAmb) hpro
  have c0 : cpsTripleWithin 2 (pc 0) (pc 2) fullCodeHo
      (hoEntryTempsNE ** hoEntryPreNE sp0 raVal bodyPtr typeW destPtr body outOld A **
        hoShaCalleeAmbNE vals st0 scratch0 iv params)
      (hoEntryTempsNE ** hoAfterPrologue newSp raVal bodyPtr typeW nW destPtr
        body ((0 : BitVec 8) :: body) outOld (stackFree newSp 6 ** A) **
        hoShaCalleeAmbNE vals st0 scratch0 iv params) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [hoEntryPreNE, nW, n] at hp
        xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq)
      hproF
  -- la
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (0 : Word)) **
      (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x29 ↦ᵣ (0 : Word)) ** hoShaCalleeAmbNE vals st0 scratch0 iv params)
    (by
      refine pcFree_sepConj pcFree_regIs <|
        pcFree_sepConj pcFree_regIs <|
          pcFree_sepConj pcFree_regIs <|
            pcFree_sepConj pcFree_regIs <|
              pcFree_sepConj pcFree_regIs <|
                pcFree_sepConj pcFree_regIs <|
                  pcFree_sepConj pcFree_regIs hAmb)
    hla
  have c1 : cpsTripleWithin 3 (pc 2) (pc 5) fullCodeHo
      (hoEntryTempsNE ** hoAfterPrologue newSp raVal bodyPtr typeW nW destPtr
        body ((0 : BitVec 8) :: body) outOld (stackFree newSp 6 ** A) **
        hoShaCalleeAmbNE vals st0 scratch0 iv params)
      ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x29 ↦ᵣ (0 : Word)) **
        hoAfterType newSp raVal bodyPtr typeW nW destPtr
          body body outOld (stackFree newSp 6 ** A) **
        hoShaCalleeAmbNE vals st0 scratch0 iv params) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [hoEntryTempsNE] at hp
        xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq)
      hlaF
  -- copy setup
  have hsetupF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x29 ↦ᵣ (0 : Word)) ** hoShaCalleeAmbNE vals st0 scratch0 iv params)
    (by
      exact pcFree_sepConj pcFree_regIs <|
        pcFree_sepConj pcFree_regIs <|
          pcFree_sepConj pcFree_regIs <|
            pcFree_sepConj pcFree_regIs hAmb)
    hsetup
  have c2 : cpsTripleWithin 3 (pc 5) (pc 8) fullCodeHo
      ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x29 ↦ᵣ (0 : Word)) **
        hoAfterType newSp raVal bodyPtr typeW nW destPtr
          body body outOld (stackFree newSp 6 ** A) **
        hoShaCalleeAmbNE vals st0 scratch0 iv params)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x29 ↦ᵣ (0 : Word)) **
        hoAfterCopySetup newSp raVal bodyPtr typeW nW destPtr
          body body outOld (stackFree newSp 6 ** A) **
        hoShaCalleeAmbNE vals st0 scratch0 iv params) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq)
      hsetupF
  -- copy full
  have hcopyF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
      hoShaCalleeAmbNE vals st0 scratch0 iv params)
    (by
      exact pcFree_sepConj pcFree_regIs <|
        pcFree_sepConj pcFree_regIs <|
          pcFree_sepConj pcFree_regIs hAmb)
    hcopy
  have c3 : cpsTripleWithin (copyLoopFuel n) (pc 8) (pc 15) fullCodeHo
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x29 ↦ᵣ (0 : Word)) **
        hoAfterCopySetup newSp raVal bodyPtr typeW nW destPtr
          body body outOld (stackFree newSp 6 ** A) **
        hoShaCalleeAmbNE vals st0 scratch0 iv params)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        hoAfterCopyDone newSp raVal bodyPtr typeW nW destPtr body outOld A **
        hoShaCalleeAmbNE vals st0 scratch0 iv params) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [hoAfterCopySetupSf, nW, n] at hp ⊢
        xperm_chunked hp)
      (fun _ hq => by
        dsimp only [nW, n] at hq ⊢
        xperm_chunked hq)
      hcopyF
  -- sha ABI
  have habiF := cpsTripleWithin_frameR
    (hoShaCalleeAmbNE vals st0 scratch0 iv params) hAmb habi
  have c4 : cpsTripleWithin 4 (pc 15) (pc 19) fullCodeHo
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        hoAfterCopyDone newSp raVal bodyPtr typeW nW destPtr body outOld A **
        hoShaCalleeAmbNE vals st0 scratch0 iv params)
      (hoAfterShaAbiOwns newSp raVal bodyPtr typeW nW destPtr body outOld A **
        hoShaCalleeAmbNE vals st0 scratch0 iv params) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [nW, n] at hp
        xperm_chunked hp)
      (fun _ hq => by
        dsimp only [nW, n] at hq ⊢
        xperm_chunked hq)
      habiF
  -- discharged call
  have c5 : cpsTripleWithin (1 + nSha256 N rem) (pc 19) (pc 20) fullCodeHo
      (hoAfterShaAbiOwns newSp raVal bodyPtr typeW nW destPtr body outOld A **
        hoShaCalleeAmbNE vals st0 scratch0 iv params)
      (((.x1 ↦ᵣ (pc 20)) **
          shaCallReturn newSp Blob destPtr input) **
        hoShaResidualF29 newSp raVal bodyPtr typeW nW destPtr body A **
        hoShaExitLeftoversNE vals input params iv N rem) := by
    refine cpsTripleWithin_weaken (fun h hp => ?pre) (fun h hq => ?post) hcall
    · rw [hoShaCalleeAmbNE] at hp
      dsimp only [nW, n] at hp
      xperm_chunked hp
    · rw [hoShaExitLeftoversNE]
      dsimp only [nW, n, input] at hq ⊢
      xperm_chunked hq
  -- epi framed by leftovers
  have hepiF := cpsTripleWithin_frameR
    (hoShaExitLeftoversNE vals input params iv N rem) hLeft hepi
  have c6 : cpsTripleWithin 3 (pc 20) raVal fullCodeHo
      (((.x1 ↦ᵣ (pc 20)) **
          shaCallReturn newSp Blob destPtr input) **
        hoShaResidualF29 newSp raVal bodyPtr typeW nW destPtr body A **
        hoShaExitLeftoversNE vals input params iv N rem)
      (hoExitPostNE sp0 raVal bodyPtr typeW destPtr body A **
        hoShaExitLeftoversNE vals input params iv N rem) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [hoShaResidualF29, nW, n, input] at hp
        xperm_chunked hp)
      (fun _ hq => by
        dsimp only [hoExitPostNE, nW, n] at hq ⊢
        xperm_chunked hq)
      hepiF
  have c56 := cpsTripleWithin_seq_same_cr c5 c6
  have hall := cpsTripleWithin_seq_same_cr c0
    (cpsTripleWithin_seq_same_cr c1
      (cpsTripleWithin_seq_same_cr c2
        (cpsTripleWithin_seq_same_cr c3
          (cpsTripleWithin_seq_same_cr c4 c56))))
  have hfuel :
      2 + (3 + (3 + (copyLoopFuel n + (4 + (1 + nSha256 N rem + 3))))) =
        hashOneNonemptyFuel n N rem := by
    simp only [hashOneNonemptyFuel]; omega
  simpa [hfuel, n] using hall

end EvmAsm.Codegen.ExecutionRequestsHashHashOneNonemptyTop
