/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainF

  Nonce-station boundary assertions for `bal_account_nonstorage_finals`.
  The station occupies slots 88--134 and returns at `B + 540`, or rejects
  at the shared body exit `B + 736`.
-/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainE

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

/-- Successful nonce-station exit.  `G` is the already-materialised balance
    footprint; keeping it abstract makes preservation across nonce rejection
    explicit without duplicating `balStationPost`'s two arms. -/
def nonceStationPost (aB newSp oB : Word) (aLen fOff fSpanN : Nat)
    (n4 : Word) (acctBytes : List (BitVec 8)) (G F : Assertion) : Assertion :=
  fun h =>
    -- EMPTY arm: the prologue's zeroed nonce and code fields are unchanged.
    ((G **
      ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
      ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word)) **
      ((newSp + 48) ↦ₘ n4) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      memOwn (newSp + 64) ** memOwn (newSp + 72) **
      ((.x2 : Reg) ↦ᵣ newSp) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB) **
      regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
      regOwn .x19 ** regOwn .x20 **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
      bytesRegion aB acctBytes ** F) **
     assertPure (FieldFinal acctBytes aB fOff fSpanN none) empAssertion) h ∨
    -- FOUND arm: rlp_content_to_u64 returns the big-endian scalar in a0.
    (∃ vNext vLen : Word,
      let image := BitVec.ofNat 64 (EL.RLP.Nat.fromBytesBE
        ((acctBytes.drop (vNext - vLen - aB).toNat).take vLen.toNat))
      ((G **
        ((oB + 40) ↦ₘ (1 : Word)) ** ((oB + 48) ↦ₘ image) **
        ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
        ((oB + 72) ↦ₘ (0 : Word)) **
        ((newSp + 48) ↦ₘ n4) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        memOwn (newSp + 64) ** memOwn (newSp + 72) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
        ((.x18 : Reg) ↦ᵣ oB) **
        regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x19 ** regOwn .x20 **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
        bytesRegion aB acctBytes ** F) **
       assertPure (FieldFinal acctBytes aB fOff fSpanN (some (vNext, vLen)) ∧
        vLen.toNat ≤ 8) empAssertion) h)

/-- Shared-reject exit from station 2.  In particular, `G` and every out-block
    cell remain owned, so an earlier balance result cannot be forgotten. -/
def nonceStationRej (aB newSp oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion) : Assertion :=
  G ** memOwn (oB + 40) ** memOwn (oB + 48) **
  ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
  ((oB + 72) ↦ₘ (0 : Word)) **
  memOwn (newSp + 48) ** memOwn (newSp + 56) **
  memOwn (newSp + 64) ** memOwn (newSp + 72) **
  ((.x2 : Reg) ↦ᵣ newSp) **
  ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
  ((.x18 : Reg) ↦ᵣ oB) **
  regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
  regOwn .x19 ** regOwn .x20 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
  bytesRegion aB acctBytes ** F

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
