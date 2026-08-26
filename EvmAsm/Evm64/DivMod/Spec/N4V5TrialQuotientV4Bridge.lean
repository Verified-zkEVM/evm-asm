/-
  EvmAsm.Evm64.DivMod.Spec.N4V5TrialQuotientV4Bridge

  Bridge `divKTrialCallV5QHat = div128Quot_v4` in the call-skip no-wrap regime:
  both compute the exact 128/64 window floor there, so they coincide.  This lets
  the n=4 v5 call-skip word equality reuse the v4 EvmWord-level quotient
  correctness (`n4_call_skip_div_mod_getLimbN_v4`) by rewriting its `div128Quot_v4`
  result to `divKTrialCallV5QHat`.  Composes `divKTrialCallV5QHat_eq_qTrue` (#7606,
  v5 trial = floor) with `div128Quot_v4_eq_q_true_of_no_wrap_of_le` (v4 = floor
  under no-wrap).  Bead `evm-asm-wbc4i.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N4V5TrialQuotientExact
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.QuotientBounds

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- In the call-skip no-wrap regime (both equal the exact window floor), the v5
    trial quotient equals the v4 128/64 quotient. -/
theorem divKTrialCallV5QHat_eq_div128Quot_v4_of_no_wrap_of_le
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2 ^ 63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_pow63 : uHi.toNat < 2 ^ 63)
    (hUn21_lt_vTop : (divKTrialCallV4Un21 uHi uLo vTop).toNat < vTop.toNat)
    (h_no_wrap :
      (divKTrialCallV4Q1dd uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat ≤
        ((divKTrialCallV4Rhatdd uHi uLo vTop).toNat % 2 ^ 32) * 2 ^ 32 +
          (divKTrialCallV4Un1 uLo).toNat)
    (h_le :
      (div128Quot_v4 uHi uLo vTop).toNat ≤
        (uHi.toNat * 2 ^ 64 + uLo.toNat) / vTop.toNat) :
    divKTrialCallV5QHat uHi uLo vTop = div128Quot_v4 uHi uLo vTop := by
  apply BitVec.eq_of_toNat_eq
  rw [divKTrialCallV5QHat_eq_qTrue uHi uLo vTop hvTop_ge huHi_lt_vTop,
      div128Quot_v4_eq_q_true_of_no_wrap_of_le uHi uLo vTop
        hvTop_ge huHi_lt_vTop huHi_lt_pow63 hUn21_lt_vTop h_no_wrap h_le]

end EvmAsm.Evm64
