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

/-- Value-station entry with the two callee-saved temporaries existentially
    owned, as exposed by the outer item walk. -/
def valueStationsEntryOwn (aB newSp oB n3 l3 : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  (((((.x10 : Reg) ↦ᵣ n3) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ l3) ** ((.x2 : Reg) ↦ᵣ newSp) **
      memOwn (newSp + 64) ** memOwn (newSp + 72) **
      ((newSp + 48) ↦ₘ n3) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB) ** (oB ↦ₘ (0 : Word)) **
      ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
      ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes **
      laterFieldZeros oB F) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1) **
   regOwn .x19 ** regOwn .x20)

/-- The value-station verdict theorem does not need the incoming values of
    `x19` and `x20`; ownership is enough. -/
theorem bansf_valueStationsVerdict_own1920
    (aB newSp oB : Word) (aLen : Nat) (b0 : BitVec 8)
    (n0 l0 n1 l1 n2 l2 n3 l3 : Word)
    (acctBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hoalign : oB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hovout : oB.toNat + 80 ≤ 2 ^ 64)
    (hovalid : ∀ k, k < 80 →
      isValidByteAccess (oB + BitVec.ofNat 64 k) = true)
    (hoff3 : (n2 - aB).toNat ≤ aLen)
    (hPrefix : outerPrefix acctBytes aB aLen b0
      n0 l0 n1 l1 n2 l2 n3 l3) :
    cpsTripleWithin (((98 * (aLen + 1) + 700) +
        2 * (98 * (aLen + 1) + (7 * acctBytes.length + 800))) + 2)
      (B + 184) (B + 736) bansfCR
      (valueStationsEntryOwn aB newSp oB n3 l3 aLen acctBytes F)
      (valueStationsVerdictPost aB newSp oB n3 l3 aLen acctBytes F) := by
  unfold valueStationsEntryOwn
  refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (fun v19 v20 => ?_)
  have ht := bansf_valueStationsVerdict_spec aB newSp oB aLen b0
    n0 l0 n1 l1 n2 l2 n3 l3 v19 v20 acctBytes F hF hsalign hoalign
    hslack hover hvalid hovout hovalid hoff3 hPrefix
  exact cpsTripleWithin_weaken (by xsimp) (fun _ hp => hp) ht

#print axioms bansf_valueStationsVerdict_own1920

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
