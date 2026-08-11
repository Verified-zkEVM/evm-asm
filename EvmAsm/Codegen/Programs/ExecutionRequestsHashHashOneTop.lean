/-
  ExecutionRequestsHashHashOneTop — empty-body `erh_hash_one` under residual h_sha.

  Path: prologue → la+SB type → copy setup + BEQ empty → sha ABI → residual
  zkvm_sha256 → epi restore+ret.

  Domain: body = [] (lenW = 0). Digest = sha256 [typeByte].
  Residual h_sha = UNPROVEN-CALLEE DEPENDENCY (#12018 owns discharge).
  Parent: #12011 option B.
-/
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Programs.ExecutionRequestsHashShaResidual
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOne
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneBody
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneLa
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneEmpty
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneShaAbi
import EvmAsm.Stateless.SpecRef.Crypto

namespace EvmAsm.Codegen.ExecutionRequestsHashHashOneTop

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.ExecutionRequestsHashShaResidual
open EvmAsm.Codegen.ExecutionRequestsHashHashOne
open EvmAsm.Codegen.ExecutionRequestsHashHashOneBody
open EvmAsm.Codegen.ExecutionRequestsHashHashOneLa
open EvmAsm.Codegen.ExecutionRequestsHashHashOneEmpty
open EvmAsm.Codegen.ExecutionRequestsHashHashOneShaAbi
open EvmAsm.Stateless.SpecRef

set_option maxRecDepth 8000

/-- Empty-body fuel: 2 prolog + 3 la/sb + 4 empty + 4 sha ABI + (1+sha) + 3 epi. -/
def hashOneEmptyFuel : Nat := 2 + 3 + 4 + 4 + (1 + shaResidualFuel) + 3

theorem hashOneEmptyFuel_eq :
    hashOneEmptyFuel = 17 + shaResidualFuel := by
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

/-- Empty-body top under residual `h_sha`.
    Pre: body=[], blob scratch [0], outOld length 32, stack free 6 below newSp, ra even.
    Post: digest = sha256 [typeByte], sp/ra restored, blob = [type]. -/
theorem erh_hash_one_spec_within_empty
    (sp0 raVal bodyPtr typeW destPtr : Word)
    (outOld : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (heven : (raVal &&& ~~~(1 : Word)) = raVal)
    (_hout : outOld.length = 32)
    (h_sha : shaCallWithinShape fullCodeHo (pc 19) raVal (sp0 + (-16 : Word))
        Blob (1 : Word) destPtr
        (hashOneBlob (typeByte typeW) []) outOld
        (jalOff GuestAddrs.zkvm_sha256 (GuestAddrs.erh_hash_one + 76))
        shaResidualFuel
        (hoShaResidualF (sp0 + (-16 : Word)) raVal bodyPtr typeW (0 : Word)
          destPtr [] A)) :
    cpsTripleWithin hashOneEmptyFuel (pc 0) raVal fullCodeHo
      (hoEntryTemps ** hoEntryPreSf sp0 raVal bodyPtr typeW destPtr outOld A)
      (hoEmptyExitPost sp0 raVal bodyPtr typeW destPtr [] A) := by
  set newSp := sp0 + (-16 : Word)
  have hSf : (stackFree newSp 6 ** A).pcFree :=
    pcFree_sepConj (pcFree_stackFree _ _) hA
  have hpro := hash_one_prologue sp0 raVal bodyPtr typeW (0 : Word) destPtr
    [] [(0 : BitVec 8)] outOld (stackFree newSp 6 ** A) hSf
  have hla := hash_one_la_sb_type newSp raVal bodyPtr typeW (0 : Word) destPtr
    (0 : Word) [] [] outOld (0 : BitVec 8) (stackFree newSp 6 ** A) hSf
  have hempty := hash_one_to_sha_abi_empty newSp raVal bodyPtr typeW destPtr
    (0 : Word) (0 : Word) (0 : Word) [] [] outOld (stackFree newSp 6 ** A) hSf
  have habi := hash_one_sha_abi newSp raVal bodyPtr typeW (0 : Word) destPtr
    (0 : Word) (0 : Word) (0 : Word) [] [] outOld A hA
  have hcall := hash_one_sha_call_empty newSp raVal bodyPtr typeW destPtr
    [] outOld A hA h_sha
  have hepi := hash_one_epi_empty sp0 raVal bodyPtr typeW destPtr [] A hA heven
  -- prologue framed by temps
  have hproF := cpsTripleWithin_frameR hoEntryTemps hoEntryTemps_pcFree hpro
  have c0 : cpsTripleWithin 2 (pc 0) (pc 2) fullCodeHo
      (hoEntryTemps ** hoEntryPreSf sp0 raVal bodyPtr typeW destPtr outOld A)
      (hoEntryTemps ** hoAfterPrologue newSp raVal bodyPtr typeW (0 : Word) destPtr
        [] [(0 : BitVec 8)] outOld (stackFree newSp 6 ** A)) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [hoEntryPreSf] at hp
        xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq)
      hproF
  -- la: focus x5 from temps
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (0 : Word)) **
      (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)))
    (by
      repeat' first
        | exact pcFree_regIs
        | apply pcFree_sepConj)
    hla
  have c1 : cpsTripleWithin 3 (pc 2) (pc 5) fullCodeHo
      (hoEntryTemps ** hoAfterPrologue newSp raVal bodyPtr typeW (0 : Word) destPtr
        [] [(0 : BitVec 8)] outOld (stackFree newSp 6 ** A))
      ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        hoAfterType newSp raVal bodyPtr typeW (0 : Word) destPtr
          [] [] outOld (stackFree newSp 6 ** A)) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [hoEntryTemps] at hp
        xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq)
      hlaF
  -- empty BEQ path framed by ABI temps
  have hemptyF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)))
    (by
      exact pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs pcFree_regIs))
    hempty
  have c2 : cpsTripleWithin 4 (pc 5) (pc 15) fullCodeHo
      ((.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        hoAfterType newSp raVal bodyPtr typeW (0 : Word) destPtr
          [] [] outOld (stackFree newSp 6 ** A))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        hoAfterCopySetup newSp raVal bodyPtr typeW (0 : Word) destPtr
          [] [] outOld (stackFree newSp 6 ** A)) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq)
      hemptyF
  -- sha ABI
  have c3 : cpsTripleWithin 4 (pc 15) (pc 19) fullCodeHo
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        hoAfterCopySetup newSp raVal bodyPtr typeW (0 : Word) destPtr
          [] [] outOld (stackFree newSp 6 ** A))
      (hoAfterShaAbi newSp raVal bodyPtr typeW (0 : Word) destPtr []
        (typeByte typeW :: []) outOld A) := by
    dsimp only [hoAfterCopySetupSf] at habi
    exact habi
  have c45 := cpsTripleWithin_seq_same_cr hcall hepi
  have hall := cpsTripleWithin_seq_same_cr c0
    (cpsTripleWithin_seq_same_cr c1
      (cpsTripleWithin_seq_same_cr c2
        (cpsTripleWithin_seq_same_cr c3 c45)))
  have hfuel : 2 + (3 + (4 + (4 + (1 + shaResidualFuel + 3)))) = hashOneEmptyFuel := by
    simp only [hashOneEmptyFuel]; omega
  simpa [hfuel] using hall

end EvmAsm.Codegen.ExecutionRequestsHashHashOneTop
