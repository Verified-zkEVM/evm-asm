/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainG

  Nonce-station tuple composition (evm-asm-4ch8f.43.5).
-/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainF

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

@[irreducible]
def nonceCont496Pre (aB newSp oB n4 : Word) (aLen tEnd off : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion) : Assertion :=
  fun h => ∃ next len : Word,
    (((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
       ((.x12 : Reg) ↦ᵣ len) ** ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ next) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
       ((newSp + 48) ↦ₘ n4) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
       ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
       ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
       ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
       ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion aB acctBytes ** G ** F) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1) **
     ⌜rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
       (aB + BitVec.ofNat 64 tEnd) next len⌝) h

/-- Folded adapter from the nonce index-item success post to `Cont496`. -/
theorem nonceTupleOk_to_cont496Pre (aB newSp oB n4 : Word)
    (aLen tEnd off : Nat) (acctBytes : List (BitVec 8)) (G F : Assertion) :
    ∀ h,
      (tupleOk aB newSp tEnd off acctBytes F **
        (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
         ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
         ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
         ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
         ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20)) h →
      nonceCont496Pre aB newSp oB n4 aLen tEnd off acctBytes G F h := by
  intro h hp
  unfold tupleOk at hp
  obtain ⟨g1, g2, gd, gu, hVal, hfr⟩ := hp
  obtain ⟨next, len, hVal2⟩ := hVal
  obtain ⟨hregs, hdec⟩ := (sepConj_pure_right g1).1 hVal2
  have hR := (⟨g1, g2, gd, gu, hregs, hfr⟩ :
    (((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ len) ** ((.x2 : Reg) ↦ᵣ newSp) **
      ((newSp + 64) ↦ₘ next) **
      ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
      bytesRegion aB acctBytes ** F) **
     (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
      ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20)) h))
  delta nonceCont496Pre
  refine ⟨next, len, (sepConj_pure_right h).2 ⟨?_, hdec⟩⟩
  let L : Assertion :=
    (((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ len) ** ((.x2 : Reg) ↦ᵣ newSp) **
      ((newSp + 64) ↦ₘ next) **
      ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
      bytesRegion aB acctBytes ** F) **
     (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
      ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20)))
  let R : Assertion :=
    (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ len) ** ((.x2 : Reg) ↦ᵣ newSp) **
      ((newSp + 64) ↦ₘ next) **
      ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
      ((newSp + 48) ↦ₘ n4) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
      ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
      ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion aB acctBytes ** G ** F) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
     regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1
  have hL : L h := by dsimp only [L]; exact hR
  have heq : L = R := by dsimp only [L, R]; xperm
  change R h
  exact (congrFun heq h).mp hL

#print axioms nonceTupleOk_to_cont496Pre

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
