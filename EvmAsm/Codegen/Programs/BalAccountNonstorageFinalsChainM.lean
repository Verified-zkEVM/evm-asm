/- Top-level station composition for bal_account_nonstorage_finals. -/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainL

namespace EvmAsm.Codegen
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP
namespace BalAccountNonstorageFinalsSpec

/-- Persistent balance result carried unchanged through nonce and code stations. -/
def balResult (aB oB : Word) (fOff fSpanN : Nat)
    (acctBytes : List (BitVec 8)) : Assertion := fun h =>
  ((((oB ↦ₘ (0 : Word)) ** ((oB + 8) ↦ₘ (0 : Word)) **
      ((oB + 16) ↦ₘ (0 : Word)) ** ((oB + 24) ↦ₘ (0 : Word)) **
      ((oB + 32) ↦ₘ (0 : Word))) **
     ⌜FieldFinal acctBytes aB fOff fSpanN none⌝) h) ∨
  (∃ vNext vLen : Word,
    (((oB ↦ₘ (1 : Word)) **
      bytesRegion (oB + 8) (copyN (List.replicate 32 (0 : BitVec 8))
        acctBytes (32 - vLen.toNat) ((vNext - vLen - aB).toNat) vLen.toNat)) **
     ⌜FieldFinal acctBytes aB fOff fSpanN (some (vNext, vLen)) ∧
       vLen.toNat ≤ 32⌝) h)

/-- Split a balance-station success into its persistent result and reusable
    scratch frame. -/
theorem balStationPost_to_resultFrame
    (aB newSp oB n3 : Word) (aLen fOff fSpanN : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion) :
    ∀ h, balStationPost aB newSp oB aLen fOff fSpanN n3 acctBytes F h →
      (balResult aB oB fOff fSpanN acctBytes **
       (((newSp + 48) ↦ₘ n3) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        memOwn (newSp + 64) ** memOwn (newSp + 72) **
        ((.x2 : Reg) ↦ᵣ newSp) ** ((.x8 : Reg) ↦ᵣ aB) **
        ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB) **
        regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x19 ** regOwn .x20 ** regOwn .x5 ** regOwn .x6 **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
        bytesRegion aB acctBytes ** F)) h := by
  intro h hp
  unfold balStationPost at hp
  unfold balResult
  rcases hp with hp | hp
  · refine sepConj_mono_left (fun h' hp' => Or.inl hp') h ?_
    xperm_hyp hp
  · obtain ⟨vNext, vLen, hp⟩ := hp
    refine sepConj_mono_left (fun h' hp' => Or.inr ⟨vNext, vLen, hp'⟩) h ?_
    xperm_hyp hp

#print axioms balStationPost_to_resultFrame

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
