/-
  EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceModelBounds

  Output-bound lemmas for the pure Amsterdam blob-gas-price model.  These
  lemmas are kept separate from the recurrence definition so the base model
  remains below the Codegen file-size limit.
-/

import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceModel

set_option exponentiation.threshold 384

namespace EvmAsm.Codegen.AmsterdamBlobGasPrice

open EvmAsm EvmAsm.Rv64
open EvmAsm.Stateless.SpecRef
open EvmAsm.Evm64.EvmWord

set_option maxRecDepth 8000

/- A six-limb quotient whose value reaches the 256-bit boundary cannot have
   both high limbs zero.  The exit-divide tail uses exactly this fact: it
   rejects a completed 384-bit sum when its quotient is not representable in
   the four output limbs. -/
theorem natToLimbs_high_or_nonzero_of_ge_2pow256 (q : Nat)
    (hq : q < 2 ^ (64 * 6)) (h256 : 2 ^ 256 ≤ q) :
    (natToLimbs 6 q)[4]'(by rw [natToLimbs_length]; decide) |||
      (natToLimbs 6 q)[5]'(by rw [natToLimbs_length]; decide) ≠ (0 : Word) := by
  intro hzero
  have hboth := BitVec.or_eq_zero_iff.mp hzero
  have h4 := hboth.1
  have h5 := hboth.2
  rw [natToLimbs_getElem 6 q 4 (by decide)] at h4
  rw [natToLimbs_getElem 6 q 5 (by decide)] at h5
  have h4nat := congrArg BitVec.toNat h4
  have h5nat := congrArg BitVec.toNat h5
  simp only [BitVec.toNat_ofNat] at h4nat h5nat
  have h4nat' : (q / 2 ^ 256) % 2 ^ 64 = 0 := by
    simpa using h4nat
  have h5nat' : (q / 2 ^ 320) % 2 ^ 64 = 0 := by
    simpa using h5nat
  have hq_decomp : q % 2 ^ 256 + 2 ^ 256 * (q / 2 ^ 256) = q := by
    exact Nat.mod_add_div q (2 ^ 256)
  have hq320 : q / 2 ^ 320 = (q / 2 ^ 256) / 2 ^ 64 := by
    have hpow : (2 : Nat) ^ 320 = 2 ^ 256 * 2 ^ 64 := by
      rw [← pow_add]
    rw [hpow]
    rw [Nat.div_div_eq_div_mul]
  rw [hq320] at h5nat'
  have ht : q / 2 ^ 256 < 2 ^ 128 := by omega
  have hu : (q / 2 ^ 256) / 2 ^ 64 < 2 ^ 64 := by omega
  have ht_decomp : q / 2 ^ 256 % 2 ^ 64 +
      2 ^ 64 * ((q / 2 ^ 256) / 2 ^ 64) = q / 2 ^ 256 := by
    exact Nat.mod_add_div (q / 2 ^ 256) (2 ^ 64)
  have hzero_t : q / 2 ^ 256 = 0 := by
    have hu_mod : ((q / 2 ^ 256) / 2 ^ 64) % 2 ^ 64 = 0 := h5nat'
    have hu_mod_self :
        ((q / 2 ^ 256) / 2 ^ 64) % 2 ^ 64 =
          (q / 2 ^ 256) / 2 ^ 64 := Nat.mod_eq_of_lt hu
    have hu_zero : (q / 2 ^ 256) / 2 ^ 64 = 0 := by omega
    omega
  omega

theorem quotient_high_or_nonzero_of_oversized (S : Nat)
    (hS384 : S < taylorWord384Bound)
    (hS : taylorOutputBound ≤ S) :
    (natToLimbs 6 (S / taylorDenominator))[4]'
        (by rw [natToLimbs_length]; decide) |||
      (natToLimbs 6 (S / taylorDenominator))[5]'
        (by rw [natToLimbs_length]; decide) ≠ (0 : Word) := by
  apply natToLimbs_high_or_nonzero_of_ge_2pow256
  · exact lt_of_le_of_lt (Nat.div_le_self S taylorDenominator) hS384
  · apply (Nat.le_div_iff_mul_le (by norm_num [taylorDenominator])).2
    simpa [taylorOutputBound, taylorResultBound, Nat.mul_comm] using hS

theorem priceLoopFuel_done_oversized_quotient_high (num fuel i acc output S : Nat)
    (h_output : output < taylorWord384Bound)
    (h_done : priceLoopFuel num fuel i acc output = .done S)
    (h_oversized : taylorOutputBound ≤ S) :
    (natToLimbs 6 (S / taylorDenominator))[4]'
        (by rw [natToLimbs_length]; decide) |||
      (natToLimbs 6 (S / taylorDenominator))[5]'
        (by rw [natToLimbs_length]; decide) ≠ (0 : Word) := by
  apply quotient_high_or_nonzero_of_oversized
  · exact priceLoopFuel_done_word384_bound num fuel i acc output S
      h_output h_done
  · exact h_oversized

#print axioms natToLimbs_high_or_nonzero_of_ge_2pow256
#print axioms quotient_high_or_nonzero_of_oversized
#print axioms priceLoopFuel_done_oversized_quotient_high

end EvmAsm.Codegen.AmsterdamBlobGasPrice
