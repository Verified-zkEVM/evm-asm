/-
  Teer prior==0 block packaging (named Assumed):
  AfterPriorBeqNtaken (E+2184) → AfterPriorJoin (E+2384).

  Body: acct_absent load/BEQ; optional predelegated ADD on s10;
  20B authority==sender cmp; value_nonzero/recipient checks;
  regular_refund += 2000; MV x7,x27 joins OR-zero setup.
  Unproven mid residual packaged as TeerPriorZeroAssumed.
  Fallthrough load already: teerPriorZeroFallthrough (Prior.lean).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopPrior
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopRecover
import EvmAsm.Codegen.Programs.TxEip7702TeerScratchZero
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopField0
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic

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
    May update s10 (predelegated add) and regular_refund; posts x7=s11. -/
structure TeerPriorZeroAssumed (cr : CodeReq) where
  nSteps : Nat
  run :
    ∀ (s10Val s10New refund refundNew s11Val : Word),
      cpsTripleWithin nSteps AfterPriorBeqNtaken AfterPriorJoin cr
        ((.x26 ↦ᵣ s10Val) ** (.x27 ↦ᵣ s11Val) **
          (.x0 ↦ᵣ (0 : Word)) **
          (RegularRefundAddr ↦ₘ refund) **
          memOwn AcctAbsentAddrPz **
          memOwn AuthorityAddr **
          memOwn SenderAddrPz **
          memOwn ValueNonzeroAddrPz **
          memOwn RecipientPtrAddrPz **
          memOwn RecipientLenAddrPz **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        ((.x26 ↦ᵣ s10New) ** (.x27 ↦ᵣ s11Val) **
          (.x7 ↦ᵣ s11Val) **
          (.x0 ↦ᵣ (0 : Word)) **
          (RegularRefundAddr ↦ₘ refundNew) **
          memOwn AcctAbsentAddrPz **
          memOwn AuthorityAddr **
          memOwn SenderAddrPz **
          memOwn ValueNonzeroAddrPz **
          memOwn RecipientPtrAddrPz **
          memOwn RecipientLenAddrPz **
          regOwn .x5 ** regOwn .x6 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)

theorem teerPriorZero_run
    (asm : TeerPriorZeroAssumed teerLinkedField0)
    (s10Val s10New refund refundNew s11Val : Word) :
    cpsTripleWithin asm.nSteps AfterPriorBeqNtaken AfterPriorJoin teerLinkedField0
      ((.x26 ↦ᵣ s10Val) ** (.x27 ↦ᵣ s11Val) **
        (.x0 ↦ᵣ (0 : Word)) **
        (RegularRefundAddr ↦ₘ refund) **
        memOwn AcctAbsentAddrPz **
        memOwn AuthorityAddr **
        memOwn SenderAddrPz **
        memOwn ValueNonzeroAddrPz **
        memOwn RecipientPtrAddrPz **
        memOwn RecipientLenAddrPz **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      ((.x26 ↦ᵣ s10New) ** (.x27 ↦ᵣ s11Val) **
        (.x7 ↦ᵣ s11Val) **
        (.x0 ↦ᵣ (0 : Word)) **
        (RegularRefundAddr ↦ₘ refundNew) **
        memOwn AcctAbsentAddrPz **
        memOwn AuthorityAddr **
        memOwn SenderAddrPz **
        memOwn ValueNonzeroAddrPz **
        memOwn RecipientPtrAddrPz **
        memOwn RecipientLenAddrPz **
        regOwn .x5 ** regOwn .x6 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) :=
  asm.run s10Val s10New refund refundNew s11Val

#print axioms teerPriorZero_run

end EvmAsm.Codegen.TxEip7702TeerSpec
