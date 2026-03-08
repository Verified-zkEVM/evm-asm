/-
  EvmAsm.Evm32.Stack

  Separation logic assertions for 256-bit EVM values stored as
  8 little-endian 32-bit limbs in consecutive word-aligned memory.
-/

import EvmAsm.Evm32.Basic
import EvmAsm.Rv32.SyscallSpecs

namespace EvmAsm

open EvmWord

/-- Assert that 8 consecutive memory words hold the limbs of an EvmWord.
    The limbs are stored little-endian: addr+0 is the LSB limb, addr+28 is the MSB limb. -/
def evmWordIs (addr : Addr) (v : EvmWord) : Assertion :=
  (addr ↦ₘ v.getLimb 0) **
  ((addr + 4) ↦ₘ v.getLimb 1) **
  ((addr + 8) ↦ₘ v.getLimb 2) **
  ((addr + 12) ↦ₘ v.getLimb 3) **
  ((addr + 16) ↦ₘ v.getLimb 4) **
  ((addr + 20) ↦ₘ v.getLimb 5) **
  ((addr + 24) ↦ₘ v.getLimb 6) **
  ((addr + 28) ↦ₘ v.getLimb 7)

/-- Assert an EVM stack starting at sp. Each element is 32 bytes (8 limbs). -/
def evmStackIs (sp : Addr) (values : List EvmWord) : Assertion :=
  match values with
  | [] => empAssertion
  | v :: vs => evmWordIs sp v ** evmStackIs (sp + 32) vs

theorem pcFree_evmWordIs (addr : Addr) (v : EvmWord) :
    (evmWordIs addr v).pcFree := by
  unfold evmWordIs
  exact pcFree_sepConj (pcFree_memIs _ _)
    (pcFree_sepConj (pcFree_memIs _ _)
    (pcFree_sepConj (pcFree_memIs _ _)
    (pcFree_sepConj (pcFree_memIs _ _)
    (pcFree_sepConj (pcFree_memIs _ _)
    (pcFree_sepConj (pcFree_memIs _ _)
    (pcFree_sepConj (pcFree_memIs _ _)
                    (pcFree_memIs _ _)))))))

theorem pcFree_evmStackIs (sp : Addr) (values : List EvmWord) :
    (evmStackIs sp values).pcFree := by
  induction values generalizing sp with
  | nil => exact pcFree_emp
  | cons v vs ih => exact pcFree_sepConj (pcFree_evmWordIs sp v) (ih (sp + 32))

instance (addr : Addr) (v : EvmWord) : Assertion.PCFree (evmWordIs addr v) :=
  ⟨pcFree_evmWordIs addr v⟩

instance (sp : Addr) (values : List EvmWord) : Assertion.PCFree (evmStackIs sp values) :=
  ⟨pcFree_evmStackIs sp values⟩

theorem evmStackIs_cons (sp : Addr) (v : EvmWord) (vs : List EvmWord) :
    evmStackIs sp (v :: vs) = (evmWordIs sp v ** evmStackIs (sp + 32) vs) := rfl

theorem evmStackIs_nil (sp : Addr) :
    evmStackIs sp [] = empAssertion := rfl

end EvmAsm
