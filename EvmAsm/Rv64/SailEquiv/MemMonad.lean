/-
  EvmAsm.Rv64.SailEquiv.MemMonad

  The Sail monadic reduction (Phase 2, step #2): symbolically executing the Sail
  golden model's `execute_STORE`/`execute_LOAD` to a closed-form state update, for
  an aligned access in bare Machine mode.  Built bottom-up as per-layer `runSail_*`
  lemmas (the `runSail_jump_to` pattern in `MonadLemmas.lean`).

  This file starts with the generic loop lemma `untilFuelM_one` that the
  single-chunk (aligned) `vmem_*_addr` loop needs.
-/

import EvmAsm.Rv64.SailEquiv.MonadLemmas
import EvmAsm.Rv64.SailEquiv.MemReduce

open Sail

namespace EvmAsm.Rv64.SailEquiv

/-- `untilFuelM` with fuel 1 and a **pure** loop condition runs the body exactly
    once and returns its result (the condition is evaluated but has no effect).
    For an aligned access `split_misaligned` gives `n = 1`, so the `vmem_*_addr`
    loop is this single iteration. -/
theorem untilFuelM_one_pure {α : Type} (g : α → Bool) (init : α) (f : α → SailM α) :
    untilFuelM 1 (fun x => (Pure.pure (g x) : SailM Bool)) init f = f init := by
  unfold untilFuelM
  simp [untilFuelM.go]

/-- Sail's `writeBytes` stores byte `i` as `v.extractLsb' (8*i) 8`; our reassembly
    lemmas (`MemReduce`) are stated with `extractByte`. They coincide. -/
theorem extractByte_eq_extractLsb' (v : Word) (i : Nat) :
    extractByte v i = v.extractLsb' (8 * i) 8 := by
  simp only [extractByte, BitVec.extractLsb', Nat.mul_comm i 8]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]

end EvmAsm.Rv64.SailEquiv
