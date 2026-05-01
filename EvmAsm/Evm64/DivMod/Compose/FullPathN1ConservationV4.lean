/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1ConservationV4

  v4 trial-quotient helpers for the n=1 full path.
-/

import EvmAsm.Evm64.DivMod.Spec.V4
import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Saturated local quotient digit for an n=1 step.

If the high word is below the divisor top word, this is the exact 128/64
floor. Otherwise the hardware path uses the max trial digit `2^64 - 1`. -/
@[irreducible]
def n1LocalFloorDigit (v0 u0 uTop : Word) : Nat :=
  if BitVec.ult uTop v0 then
    (uTop.toNat * 2^64 + u0.toNat) / v0.toNat
  else
    2^64 - 1

/-- v4 raw trial quotient bounds the saturated local quotient digit. This is
    the per-step shape needed by N1 later digits: the call path only needs
    `uTop < v0`, and the max path is exact by construction. -/
theorem iterN1_v4_rawTrial_ge_local_digit
    (bltu : Bool) (v0 u0 uTop : Word)
    (hv0_ge : v0.toNat ≥ 2^63)
    (hbranch : bltu = BitVec.ult uTop v0) :
    let qHat : Word := if bltu then div128Quot_v4 uTop u0 v0 else signExtend12 4095
    n1LocalFloorDigit v0 u0 uTop ≤ qHat.toNat := by
  intro qHat
  subst qHat
  delta n1LocalFloorDigit
  cases hult : BitVec.ult uTop v0
  · have hbltu_false : bltu = false := by
      simpa [hult] using hbranch
    rw [hbltu_false]
    simp only [Bool.false_eq_true, if_false]
    rw [signExtend12_4095_toNat]
  · have hbltu_true : bltu = true := by
      simpa [hult] using hbranch
    rw [hbltu_true]
    simp only [if_true]
    have huTop_lt_v0 : uTop.toNat < v0.toNat := (EvmWord.ult_iff).mp hult
    exact div128Quot_v4_ge_q_true_normalized_of_lt uTop u0 v0 hv0_ge huTop_lt_v0

end EvmAsm.Evm64
