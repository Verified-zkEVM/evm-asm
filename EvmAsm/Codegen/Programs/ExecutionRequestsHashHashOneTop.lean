/-
  ExecutionRequestsHashHashOneTop — empty-body `erh_hash_one` with discharged sha256.

  Path: prologue → la+SB type → copy setup + BEQ empty → sha ABI →
  zkvm_sha256 (via `zkvm_sha256_spec_within`, no residual `h_sha`) → epi.

  Domain: body = [] (lenW = 0). Digest = sha256 [typeByte].
  Callee BSS + `regsAt` + x29/x30 owns live in ambient (guest-image / accel hyps).
  Parent: #12011 option B. Owner #12018.
-/
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Programs.ExecutionRequestsHashShaResidual
import EvmAsm.Codegen.Programs.ExecutionRequestsHashShaDischarge
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOne
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneBody
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneLa
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneEmpty
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneShaAbi
import EvmAsm.Codegen.Proofs.HashBridgeSha256Top
import EvmAsm.Stateless.SpecRef.Crypto

namespace EvmAsm.Codegen.ExecutionRequestsHashHashOneTop

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
open EvmAsm.Codegen.Proofs
open EvmAsm.Stateless.SpecRef

set_option maxRecDepth 8000

/-- Empty-body fuel: 2 prolog + 3 la/sb + 4 empty + 4 sha ABI + (1+nSha) + 3 epi. -/
def hashOneEmptyFuel : Nat := 2 + 3 + 4 + 4 + (1 + nSha256 0 1) + 3

theorem hashOneEmptyFuel_eq :
    hashOneEmptyFuel = 17 + nSha256 0 1 := by
  simp only [hashOneEmptyFuel]; omega

/-- Entry with stackFree below newSp (needed by residual sha frame).
    Blob starts as a single scratch byte (overwritten by SB type). -/
def hoEntryPreSf (sp0 raVal bodyPtr typeW destPtr : Word)
    (outBytes : List (BitVec 8)) (A : Assertion) : Assertion :=
  let newSp := sp0 + (-16 : Word)
  hoEntryPre sp0 raVal bodyPtr typeW (0 : Word) destPtr [] [(0 : BitVec 8)] outBytes
    (stackFree newSp 6 ** A)

/-- Scratch temps owned at empty-body entry (zeroed). -/
def hoEntryTemps : Assertion :=
  (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
  (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
  (.x28 ↦ᵣ (0 : Word))

theorem hoEntryTemps_pcFree : hoEntryTemps.pcFree := by
  simp only [hoEntryTemps]
  repeat' first
    | exact pcFree_regIs
    | apply pcFree_sepConj

/-- Callee-side ambient preserved through the empty path until the sha call:
    frame regs, BSS, and free temps x29/x30 (x5–x7/x28 arrive via entry temps). -/
@[irreducible] def hoShaCalleeAmb (vals : Reg → Word)
    (st0 scratch0 iv params : List (BitVec 8)) : Assertion :=
  let ShaSt : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_state
  let ShaIvA : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_iv
  let ShaIn : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_input
  let ShaPar : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_params
  regsAt sha256Frame vals **
    bytesRegion ShaSt st0 ** bytesRegion ShaIvA iv **
    bytesRegion ShaIn scratch0 ** bytesRegion ShaPar params **
    regOwn .x29 ** regOwn .x30

theorem hoShaCalleeAmb_pcFree (vals : Reg → Word)
    (st0 scratch0 iv params : List (BitVec 8)) :
    (hoShaCalleeAmb vals st0 scratch0 iv params).pcFree := by
  simp only [hoShaCalleeAmb]
  exact pcFree_sepConj (pcFree_regsAt _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) <|
        pcFree_sepConj (bytesRegion_pcFree _ _) <|
          pcFree_sepConj (bytesRegion_pcFree _ _) <|
            pcFree_sepConj pcFree_regOwn pcFree_regOwn

/-- Exit leftovers after discharged sha (callee BSS finals + frame regs + x29/x30). -/
@[irreducible] def hoShaExitLeftovers (vals : Reg → Word)
    (input params iv : List (BitVec 8)) : Assertion :=
  regsAt sha256Frame vals **
    shaBssPost input params iv 0 1 **
    regOwn .x29 ** regOwn .x30

theorem hoShaExitLeftovers_pcFree (vals : Reg → Word)
    (input params iv : List (BitVec 8)) :
    (hoShaExitLeftovers vals input params iv).pcFree := by
  simp only [hoShaExitLeftovers]
  exact pcFree_sepConj (pcFree_regsAt _ _) <|
    pcFree_sepConj (shaBssPost_pcFree _ _ _ _ _) <|
      pcFree_sepConj pcFree_regOwn pcFree_regOwn

/-- Empty-body top discharged via `zkvm_sha256_spec_within` (no residual `h_sha`).
    Pre: body=[], blob scratch [0], outOld length 32, stack free 6 below newSp, ra even,
    plus callee ambient (regsAt/BSS/x29/x30) and `ShaDischargeHyps` (named accel assumptions).
    Post: digest = sha256 [typeByte], sp/ra restored, blob = [type], callee leftovers preserved. -/
theorem erh_hash_one_spec_within_empty
    (sp0 raVal bodyPtr typeW destPtr : Word)
    (outOld : List (BitVec 8))
    (v8 v9 v18 v19 v20 v21 : Word)
    (st0 scratch0 iv params : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (heven : (raVal &&& ~~~(1 : Word)) = raVal)
    (hout : outOld.length = 32)
    (hyps : shaDischargeHyps_empty destPtr (typeByte typeW) st0 scratch0 iv params) :
    let vals := sha256EntryVals v8 v9 v18 v19 v20 v21
    let input := hashOneBlob (typeByte typeW) []
    cpsTripleWithin hashOneEmptyFuel (pc 0) raVal fullCodeHo
      (hoEntryTemps ** hoEntryPreSf sp0 raVal bodyPtr typeW destPtr outOld A **
        hoShaCalleeAmb vals st0 scratch0 iv params)
      (hoEmptyExitPost sp0 raVal bodyPtr typeW destPtr [] A **
        hoShaExitLeftovers vals input params iv) := by
  intro vals input
  set newSp := sp0 + (-16 : Word)
  have hSf : (stackFree newSp 6 ** A).pcFree :=
    pcFree_sepConj (pcFree_stackFree _ _) hA
  have hAmb := hoShaCalleeAmb_pcFree vals st0 scratch0 iv params
  have hLeft := hoShaExitLeftovers_pcFree vals input params iv
  have hpro := hash_one_prologue sp0 raVal bodyPtr typeW (0 : Word) destPtr
    [] [(0 : BitVec 8)] outOld (stackFree newSp 6 ** A) hSf
  have hla := hash_one_la_sb_type newSp raVal bodyPtr typeW (0 : Word) destPtr
    (0 : Word) [] [] outOld (0 : BitVec 8) (stackFree newSp 6 ** A) hSf
  have hempty := hash_one_to_sha_abi_empty newSp raVal bodyPtr typeW destPtr
    (0 : Word) (0 : Word) (0 : Word) [] [] outOld (stackFree newSp 6 ** A) hSf
  have habi := hash_one_sha_abi newSp raVal bodyPtr typeW (0 : Word) destPtr
    (0 : Word) (0 : Word) (0 : Word) [] [] outOld A hA
  have hcall := hash_one_sha_call_empty newSp raVal bodyPtr typeW destPtr
    outOld v8 v9 v18 v19 v20 v21 st0 scratch0 iv params A hA hyps hout
  have hepi := hash_one_epi_empty sp0 raVal bodyPtr typeW destPtr [] A hA heven
  -- prologue framed by temps + callee ambient
  have hproF := cpsTripleWithin_frameR
    (hoEntryTemps ** hoShaCalleeAmb vals st0 scratch0 iv params)
    (pcFree_sepConj hoEntryTemps_pcFree hAmb) hpro
  have c0 : cpsTripleWithin 2 (pc 0) (pc 2) fullCodeHo
      (hoEntryTemps ** hoEntryPreSf sp0 raVal bodyPtr typeW destPtr outOld A **
        hoShaCalleeAmb vals st0 scratch0 iv params)
      (hoEntryTemps ** hoAfterPrologue newSp raVal bodyPtr typeW (0 : Word) destPtr
        [] [(0 : BitVec 8)] outOld (stackFree newSp 6 ** A) **
        hoShaCalleeAmb vals st0 scratch0 iv params) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [hoEntryPreSf] at hp
        xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq)
      hproF
  -- la: focus x5 from temps; frame remaining temps + callee ambient
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (0 : Word)) **
      (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
      hoShaCalleeAmb vals st0 scratch0 iv params)
    (by
      refine pcFree_sepConj pcFree_regIs <|
        pcFree_sepConj pcFree_regIs <|
          pcFree_sepConj pcFree_regIs <|
            pcFree_sepConj pcFree_regIs <|
              pcFree_sepConj pcFree_regIs <|
                pcFree_sepConj pcFree_regIs hAmb)
    hla
  have c1 : cpsTripleWithin 3 (pc 2) (pc 5) fullCodeHo
      (hoEntryTemps ** hoAfterPrologue newSp raVal bodyPtr typeW (0 : Word) destPtr
        [] [(0 : BitVec 8)] outOld (stackFree newSp 6 ** A) **
        hoShaCalleeAmb vals st0 scratch0 iv params)
      ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        hoAfterType newSp raVal bodyPtr typeW (0 : Word) destPtr
          [] [] outOld (stackFree newSp 6 ** A) **
        hoShaCalleeAmb vals st0 scratch0 iv params) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [hoEntryTemps] at hp
        xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq)
      hlaF
  -- empty BEQ path framed by ABI temps + callee ambient
  have hemptyF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
      hoShaCalleeAmb vals st0 scratch0 iv params)
    (by
      exact pcFree_sepConj pcFree_regIs <|
        pcFree_sepConj pcFree_regIs <|
          pcFree_sepConj pcFree_regIs hAmb)
    hempty
  have c2 : cpsTripleWithin 4 (pc 5) (pc 15) fullCodeHo
      ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        hoAfterType newSp raVal bodyPtr typeW (0 : Word) destPtr
          [] [] outOld (stackFree newSp 6 ** A) **
        hoShaCalleeAmb vals st0 scratch0 iv params)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        hoAfterCopySetup newSp raVal bodyPtr typeW (0 : Word) destPtr
          [] [] outOld (stackFree newSp 6 ** A) **
        hoShaCalleeAmb vals st0 scratch0 iv params) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq)
      hemptyF
  -- sha ABI framed by callee ambient
  have habiF := cpsTripleWithin_frameR
    (hoShaCalleeAmb vals st0 scratch0 iv params) hAmb habi
  have c3 : cpsTripleWithin 4 (pc 15) (pc 19) fullCodeHo
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        hoAfterCopySetupSf newSp raVal bodyPtr typeW (0 : Word) destPtr
          [] [] outOld A **
        hoShaCalleeAmb vals st0 scratch0 iv params)
      (hoAfterShaAbi newSp raVal bodyPtr typeW (0 : Word) destPtr []
        (typeByte typeW :: []) outOld A **
        hoShaCalleeAmb vals st0 scratch0 iv params) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq)
      habiF
  -- Bridge c2 post (expanded setup) → c3 pre (Sf)
  have c2' : cpsTripleWithin 4 (pc 5) (pc 15) fullCodeHo
      ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        hoAfterType newSp raVal bodyPtr typeW (0 : Word) destPtr
          [] [] outOld (stackFree newSp 6 ** A) **
        hoShaCalleeAmb vals st0 scratch0 iv params)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        hoAfterCopySetupSf newSp raVal bodyPtr typeW (0 : Word) destPtr
          [] [] outOld A **
        hoShaCalleeAmb vals st0 scratch0 iv params) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hq => by
        dsimp only [hoAfterCopySetupSf] at hq ⊢
        xperm_chunked hq)
      c2
  -- discharged call: reshape callee amb into flat BSS/regs used by call lemma
  have c4 : cpsTripleWithin (1 + nSha256 0 1) (pc 19) (pc 20) fullCodeHo
      (hoAfterShaAbi newSp raVal bodyPtr typeW (0 : Word) destPtr []
        (typeByte typeW :: []) outOld A **
        hoShaCalleeAmb vals st0 scratch0 iv params)
      (((.x1 ↦ᵣ (pc 20)) **
          shaCallReturn newSp Blob destPtr input) **
        hoShaResidualF newSp raVal bodyPtr typeW (0 : Word) destPtr [] A **
        hoShaExitLeftovers vals input params iv) := by
    refine cpsTripleWithin_weaken (fun h hp => ?pre) (fun h hq => ?post) hcall
    · rw [hoShaCalleeAmb] at hp
      xperm_chunked hp
    · rw [hoShaExitLeftovers]
      xperm_chunked hq
  -- epi framed by exit leftovers
  have hepiF := cpsTripleWithin_frameR
    (hoShaExitLeftovers vals input params iv) hLeft hepi
  have c5 : cpsTripleWithin 3 (pc 20) raVal fullCodeHo
      (((.x1 ↦ᵣ (pc 20)) **
          shaCallReturn newSp Blob destPtr input) **
        hoShaResidualF newSp raVal bodyPtr typeW (0 : Word) destPtr [] A **
        hoShaExitLeftovers vals input params iv)
      (hoEmptyExitPost sp0 raVal bodyPtr typeW destPtr [] A **
        hoShaExitLeftovers vals input params iv) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq)
      hepiF
  have hall := cpsTripleWithin_seq_same_cr c0
    (cpsTripleWithin_seq_same_cr c1
      (cpsTripleWithin_seq_same_cr c2'
        (cpsTripleWithin_seq_same_cr c3
          (cpsTripleWithin_seq_same_cr c4 c5))))
  -- Keep `nSha256` opaque: it is an `abbrev` and unfolding into `omega` times out.
  have hfuel :
      2 + (3 + (4 + (4 + (1 + nSha256 0 1 + 3)))) = hashOneEmptyFuel := by
    simp only [hashOneEmptyFuel]; omega
  simpa [hfuel] using hall

end EvmAsm.Codegen.ExecutionRequestsHashHashOneTop
