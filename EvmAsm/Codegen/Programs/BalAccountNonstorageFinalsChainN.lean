/- Top-level SEG-B and ABI assembly for bal_account_nonstorage_finals. -/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainM

namespace EvmAsm.Codegen
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP
namespace BalAccountNonstorageFinalsSpec

/-- State preserved ambiently while the outer items 0--3 are walked. -/
def valueEntryAmbient (aB newSp oB : Word) (aLen : Nat)
    (F : Assertion) : Assertion :=
  memOwn (newSp + 64) ** memOwn (newSp + 72) **
  ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
  ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
  (oB ↦ₘ (0 : Word)) ** ((oB + 8) ↦ₘ (0 : Word)) **
  ((oB + 16) ↦ₘ (0 : Word)) ** ((oB + 24) ↦ₘ (0 : Word)) **
  ((oB + 32) ↦ₘ (0 : Word)) ** ((oB + 40) ↦ₘ (0 : Word)) **
  ((oB + 48) ↦ₘ (0 : Word)) ** ((oB + 56) ↦ₘ (0 : Word)) **
  ((oB + 64) ↦ₘ (0 : Word)) ** ((oB + 72) ↦ₘ (0 : Word)) ** F

/-- The outer-item ambient footprint is PC-free when its caller frame is. -/
theorem valueEntryAmbient_pcFree
    (aB newSp oB : Word) (aLen : Nat) (F : Assertion) (hF : F.pcFree) :
    (valueEntryAmbient aB newSp oB aLen F).pcFree := by
  letI : Assertion.PCFree F := ⟨hF⟩
  unfold valueEntryAmbient
  exact (inferInstance : Assertion.PCFree _).proof

#print axioms valueEntryAmbient_pcFree

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
