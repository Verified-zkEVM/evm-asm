/-
  EvmAsm.Evm64.DivMod.Compose.Dispatcher

  Dispatcher-level scaffold for the bounded DIV/MOD limb specs.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1LoopUnified
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Full
import EvmAsm.Evm64.DivMod.Compose.FullPathN3LoopUnified
import EvmAsm.Evm64.DivMod.Compose.FullPathN4
import EvmAsm.Evm64.DivMod.Compose.FullPathN4Beq
import EvmAsm.Evm64.DivMod.Compose.FullPathN4Shift0
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN1LoopUnified
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN2LoopUnified
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN3LoopUnified
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN4
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN4Shift0

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Dispatcher-facing DIV code requirement. Kept as a named alias so future
    dispatcher proofs can depend on a stable surface instead of unfolding
    `divCode` at every call site. -/
abbrev divDispatcherCode (base : Word) : CodeReq :=
  divCode base

/-- Dispatcher-facing MOD code requirement. -/
abbrev modDispatcherCode (base : Word) : CodeReq :=
  modCode base

theorem divDispatcherCode_sub_divCode {base : Word} :
    ∀ a i, (divDispatcherCode base) a = some i → (divCode base) a = some i := by
  intro a i h
  exact h

theorem modDispatcherCode_sub_modCode {base : Word} :
    ∀ a i, (modDispatcherCode base) a = some i → (modCode base) a = some i := by
  intro a i h
  exact h

theorem sharedDivModCode_sub_divDispatcherCode {base : Word} :
    ∀ a i, (sharedDivModCode base) a = some i → (divDispatcherCode base) a = some i :=
  sharedDivModCode_sub_divCode

theorem sharedDivModCode_sub_modDispatcherCode {base : Word} :
    ∀ a i, (sharedDivModCode base) a = some i → (modDispatcherCode base) a = some i :=
  sharedDivModCode_sub_modCode

inductive DivDispatchBranch where
  | bzero
  | n1Full
  | n2Full
  | n3Full
  | n4MaxSkip
  | n4CallSkip
  | n4MaxAddbackBeq
  | n4CallAddbackBeq
  | n4Shift0CallSkip
  | n4Shift0CallAddbackBeq
  deriving DecidableEq, Repr

inductive ModDispatchBranch where
  | bzero
  | n1Full
  | n2Full
  | n3Full
  | n4MaxSkip
  | n4CallSkip
  | n4CallAddbackBeq
  | n4Shift0CallSkip
  | n4Shift0CallAddbackBeq
  deriving DecidableEq, Repr

def DivDispatchBranch.bound : DivDispatchBranch → Nat
  | .bzero => 13
  | .n1Full => 946
  | .n2Full => 744
  | .n3Full => 542
  | .n4MaxSkip => 214
  | .n4CallSkip => 264
  | .n4MaxAddbackBeq => 290
  | .n4CallAddbackBeq => 340
  | .n4Shift0CallSkip => 208
  | .n4Shift0CallAddbackBeq => 284

def ModDispatchBranch.bound : ModDispatchBranch → Nat
  | .bzero => 13
  | .n1Full => 946
  | .n2Full => 744
  | .n3Full => 542
  | .n4MaxSkip => 214
  | .n4CallSkip => 264
  | .n4CallAddbackBeq => 340
  | .n4Shift0CallSkip => 208
  | .n4Shift0CallAddbackBeq => 284

end EvmAsm.Evm64
