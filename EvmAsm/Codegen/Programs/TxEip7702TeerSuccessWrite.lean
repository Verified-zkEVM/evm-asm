/-
  Teer success-table write path packaging (named Assumed):
  AtSuccessCount (E+2708) → AfterAuthLoopLi (E+724) via JAL loop-back,
  or → AtLoopExit when the auth-list scan is complete (caller chooses).

  Body: load success_count; BGEU cap; scale; copy authority→table[i];
  set present/nonce; inc count; inc s8; JAL back to auth-loop BEQ.
  Unproven mid-loop residual packaged as TeerSuccessWriteAssumed.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopOrZero
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopBeq
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopRecover
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopField0
import EvmAsm.Codegen.Programs.TxEip7702TeerScratchZero
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

/-- Named hyp: success-table write + s8++ + JAL back to AfterAuthLoopLi.
    Covers AtSuccessCount → AfterAuthLoopLi under ambient temps/scratch. -/
structure TeerSuccessWriteAssumed (cr : CodeReq) where
  nSteps : Nat
  /-- Write path that returns to the auth-loop header (s8 increased by 1). -/
  loop_back :
    ∀ (s8Val s10Val spC : Word),
      cpsTripleWithin nSteps AtSuccessCount AfterAuthLoopLi cr
        ((.x24 ↦ᵣ s8Val) ** (.x26 ↦ᵣ s10Val) ** (.x2 ↦ᵣ spC) **
          (.x0 ↦ᵣ (0 : Word)) **
          memOwn SuccessCountAddr **
          memOwn AuthorityAddr **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        ((.x24 ↦ᵣ (s8Val + (1 : Word))) ** (.x26 ↦ᵣ s10Val) ** (.x2 ↦ᵣ spC) **
          (.x0 ↦ᵣ (0 : Word)) **
          memOwn SuccessCountAddr **
          memOwn AuthorityAddr **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)

/-- Thin wrapper applying the Assumed loop-back arm. -/
theorem teerSuccessWrite_loopBack
    (asm : TeerSuccessWriteAssumed teerLinkedField0)
    (s8Val s10Val spC : Word) :
    cpsTripleWithin asm.nSteps AtSuccessCount AfterAuthLoopLi teerLinkedField0
      ((.x24 ↦ᵣ s8Val) ** (.x26 ↦ᵣ s10Val) ** (.x2 ↦ᵣ spC) **
        (.x0 ↦ᵣ (0 : Word)) **
        memOwn SuccessCountAddr **
        memOwn AuthorityAddr **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      ((.x24 ↦ᵣ (s8Val + (1 : Word))) ** (.x26 ↦ᵣ s10Val) ** (.x2 ↦ᵣ spC) **
        (.x0 ↦ᵣ (0 : Word)) **
        memOwn SuccessCountAddr **
        memOwn AuthorityAddr **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) :=
  asm.loop_back s8Val s10Val spC

#print axioms teerSuccessWrite_loopBack

end EvmAsm.Codegen.TxEip7702TeerSpec
