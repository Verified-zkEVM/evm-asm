/- ABI post normalization for bal_account_nonstorage_finals. -/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainN

namespace EvmAsm.Codegen
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP
namespace BalAccountNonstorageFinalsSpec

/-- Common conservative result footprint of every parse-reject path. -/
def bansfRejectResult (aB newSp oB : Word) (acctBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (1 : Word)) **
  memOwn (newSp + 48) ** memOwn (newSp + 56) **
  memOwn (newSp + 64) ** memOwn (newSp + 72) **
  memOwn oB ** memOwn (oB + 8) ** memOwn (oB + 16) **
  memOwn (oB + 24) ** memOwn (oB + 32) ** memOwn (oB + 40) **
  memOwn (oB + 48) ** memOwn (oB + 56) ** memOwn (oB + 64) **
  memOwn (oB + 72) ** regOwn .x11 ** regOwn .x12 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes ** F

private def zeroOutBlock (oB : Word) : Assertion :=
  (oB ↦ₘ (0 : Word)) ** ((oB + 8) ↦ₘ (0 : Word)) **
  ((oB + 16) ↦ₘ (0 : Word)) ** ((oB + 24) ↦ₘ (0 : Word)) **
  ((oB + 32) ↦ₘ (0 : Word)) ** ((oB + 40) ↦ₘ (0 : Word)) **
  ((oB + 48) ↦ₘ (0 : Word)) ** ((oB + 56) ↦ₘ (0 : Word)) **
  ((oB + 64) ↦ₘ (0 : Word)) ** ((oB + 72) ↦ₘ (0 : Word))

private def ownOutBlock (oB : Word) : Assertion :=
  memOwn oB ** memOwn (oB + 8) ** memOwn (oB + 16) **
  memOwn (oB + 24) ** memOwn (oB + 32) ** memOwn (oB + 40) **
  memOwn (oB + 48) ** memOwn (oB + 56) ** memOwn (oB + 64) **
  memOwn (oB + 72)

private def earlyRejectRest (aB newSp : Word)
    (acctBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
  memOwn (newSp + 48) ** memOwn (newSp + 56) **
  memOwn (newSp + 64) ** memOwn (newSp + 72) **
  regOwn .x19 ** regOwn .x20 ** regOwn .x11 ** regOwn .x12 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
  bytesRegion aB acctBytes ** F

/-- SEG-B's earliest reject factors into the ABI-restorable register set and
    the common conservative reject result. -/
theorem chainRejB_to_abiReject
    (aB newSp oB : Word) (aLen : Nat) (acctBytes : List (BitVec 8))
    (F : Assertion) :
    ∀ h, chainRejB aB newSp oB aLen acctBytes
        (memOwn (newSp + 64) ** memOwn (newSp + 72) **
         regOwn .x19 ** regOwn .x20 ** F) h →
      (((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt bansfFrame **
        bansfRejectResult aB newSp oB acctBytes F) h := by
  intro h hp
  unfold chainRejB at hp
  have hq :
      (((((.x8 : Reg) ↦ᵣ aB) **
          ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen)) **
          ((.x18 : Reg) ↦ᵣ oB)) **
       (zeroOutBlock oB ** earlyRejectRest aB newSp acctBytes F)) h := by
    unfold zeroOutBlock earlyRejectRest
    xperm_hyp hp
  have hAnchors : ∀ h',
      (((((.x8 : Reg) ↦ᵣ aB) **
          ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen)) **
          ((.x18 : Reg) ↦ᵣ oB)) h') →
      (((regOwn .x8 ** regOwn .x9) ** regOwn .x18) h') :=
    sepConj_mono (sepConj_mono (regIs_implies_regOwn .x8)
      (regIs_implies_regOwn .x9)) (regIs_implies_regOwn .x18)
  have hOut : ∀ h',
      zeroOutBlock oB h' → ownOutBlock oB h' := by
    unfold zeroOutBlock ownOutBlock
    exact sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn
            (sepConj_mono memIs_implies_memOwn
              (sepConj_mono memIs_implies_memOwn
                (sepConj_mono memIs_implies_memOwn
                  (sepConj_mono memIs_implies_memOwn
                    (sepConj_mono memIs_implies_memOwn
                      memIs_implies_memOwn))))))))
  have hq' := sepConj_mono hAnchors
    (sepConj_mono hOut (fun _ hx => hx)) h hq
  unfold earlyRejectRest ownOutBlock at hq'
  unfold bansfRejectResult
  simp only [regsOwnAt, bansfFrame, List.foldr, sepConj_emp_right']
  xperm_hyp hq'

#print axioms chainRejB_to_abiReject

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
