/-
  Teer prior==0 block packaging (named Assumed):
  AfterPriorBeqNtaken (E+2184) → AfterPriorJoin (E+2384).

  Body: acct_absent load/BEQ; optional predelegated ADD on s10;
  20B authority==sender cmp; value_nonzero/recipient checks;
  regular_refund += 2000; join OrZero setup.

  Filled path: absent=0 + auth==sender full match (teerPzLoop20).
  Other arms (absent≠0, mismatch→value/refund) residual.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopPrior
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopRecover
import EvmAsm.Codegen.Programs.TxEip7702TeerScratchZero
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopField0
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

def AcctAbsentAddrPz : Word := BitVec.ofNat 64 GuestAddrs.teer_acct_absent
def ValueNonzeroAddrPz : Word := BitVec.ofNat 64 GuestAddrs.teer_value_nonzero
def RecipientPtrAddrPz : Word := BitVec.ofNat 64 GuestAddrs.teer_recipient_ptr
def RecipientLenAddrPz : Word := BitVec.ofNat 64 GuestAddrs.teer_recipient_len
def SenderAddrPz : Word := BitVec.ofNat 64 GuestAddrs.bv_stx_sender_addr

/-- Named hyp: prior==0 block AfterPriorBeqNtaken → AfterPriorJoin.
    Match path: acct_absent=0, authority bytes = sender bytes (len 20).
    s10 and regular_refund unchanged; x7 ends at AuthorityAddr+20. -/
structure TeerPriorZeroAssumed (cr : CodeReq) where
  nSteps : Nat
  run_authMatch :
    ∀ (s10Val refund s11Val ghost6 : Word)
      (authBytes senderBytes : List (BitVec 8)),
      authBytes.length = 20 →
      authBytes = senderBytes →
      AuthorityAddr.toNat % 8 = 0 →
      SenderAddrPz.toNat % 8 = 0 →
      AuthorityAddr.toNat + 20 ≤ 2 ^ 64 →
      SenderAddrPz.toNat + 20 ≤ 2 ^ 64 →
      (∀ j, j < 20 →
        isValidByteAccess (AuthorityAddr + BitVec.ofNat 64 j) = true) →
      (∀ j, j < 20 →
        isValidByteAccess (SenderAddrPz + BitVec.ofNat 64 j) = true) →
      cpsTripleWithin nSteps AfterPriorBeqNtaken AfterPriorJoin cr
        ((.x26 ↦ᵣ s10Val) ** (.x27 ↦ᵣ s11Val) **
          (.x0 ↦ᵣ (0 : Word)) **
          (.x6 ↦ᵣ ghost6) **
          (RegularRefundAddr ↦ₘ refund) **
          (AcctAbsentAddrPz ↦ₘ (0 : Word)) **
          bytesRegion AuthorityAddr authBytes **
          bytesRegion SenderAddrPz senderBytes **
          memOwn ValueNonzeroAddrPz **
          memOwn RecipientPtrAddrPz **
          memOwn RecipientLenAddrPz **
          regOwn .x5 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        ((.x26 ↦ᵣ s10Val) ** (.x27 ↦ᵣ s11Val) **
          (.x0 ↦ᵣ (0 : Word)) **
          (.x6 ↦ᵣ ghost6) **
          (.x7 ↦ᵣ (AuthorityAddr + (20 : Word))) **
          (.x28 ↦ᵣ (SenderAddrPz + (20 : Word))) **
          (.x29 ↦ᵣ (0 : Word)) **
          (RegularRefundAddr ↦ₘ refund) **
          (AcctAbsentAddrPz ↦ₘ (0 : Word)) **
          bytesRegion AuthorityAddr authBytes **
          bytesRegion SenderAddrPz senderBytes **
          memOwn ValueNonzeroAddrPz **
          memOwn RecipientPtrAddrPz **
          memOwn RecipientLenAddrPz **
          regOwn .x5 ** regOwn .x30 ** regOwn .x31)

theorem teerPriorZero_run_authMatch
    (asm : TeerPriorZeroAssumed teerLinkedField0)
    (s10Val refund s11Val ghost6 : Word)
    (authBytes senderBytes : List (BitVec 8))
    (hlen : authBytes.length = 20) (heq : authBytes = senderBytes)
    (halignA : AuthorityAddr.toNat % 8 = 0)
    (halignS : SenderAddrPz.toNat % 8 = 0)
    (hoverA : AuthorityAddr.toNat + 20 ≤ 2 ^ 64)
    (hoverS : SenderAddrPz.toNat + 20 ≤ 2 ^ 64)
    (hvalidA : ∀ j, j < 20 →
      isValidByteAccess (AuthorityAddr + BitVec.ofNat 64 j) = true)
    (hvalidS : ∀ j, j < 20 →
      isValidByteAccess (SenderAddrPz + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin asm.nSteps AfterPriorBeqNtaken AfterPriorJoin teerLinkedField0
      ((.x26 ↦ᵣ s10Val) ** (.x27 ↦ᵣ s11Val) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ ghost6) **
        (RegularRefundAddr ↦ₘ refund) **
        (AcctAbsentAddrPz ↦ₘ (0 : Word)) **
        bytesRegion AuthorityAddr authBytes **
        bytesRegion SenderAddrPz senderBytes **
        memOwn ValueNonzeroAddrPz **
        memOwn RecipientPtrAddrPz **
        memOwn RecipientLenAddrPz **
        regOwn .x5 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      ((.x26 ↦ᵣ s10Val) ** (.x27 ↦ᵣ s11Val) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ ghost6) **
        (.x7 ↦ᵣ (AuthorityAddr + (20 : Word))) **
        (.x28 ↦ᵣ (SenderAddrPz + (20 : Word))) **
        (.x29 ↦ᵣ (0 : Word)) **
        (RegularRefundAddr ↦ₘ refund) **
        (AcctAbsentAddrPz ↦ₘ (0 : Word)) **
        bytesRegion AuthorityAddr authBytes **
        bytesRegion SenderAddrPz senderBytes **
        memOwn ValueNonzeroAddrPz **
        memOwn RecipientPtrAddrPz **
        memOwn RecipientLenAddrPz **
        regOwn .x5 ** regOwn .x30 ** regOwn .x31) :=
  asm.run_authMatch s10Val refund s11Val ghost6 authBytes senderBytes
    hlen heq halignA halignS hoverA hoverS hvalidA hvalidS

#print axioms teerPriorZero_run_authMatch

end EvmAsm.Codegen.TxEip7702TeerSpec
