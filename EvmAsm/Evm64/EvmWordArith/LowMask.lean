/-
  EvmAsm.Evm64.EvmWordArith.LowMask

  Low-mask bridge: `v &&& (2^k - 1) = 0 ↔ 2^k ∣ v.toNat`.  This is the
  semantic tie behind power-of-two multiple checks such as the guest's
  `value &&& (GAS_PER_BLOB - 1) = 0` (chainValidateBlobGasUsedMultiple).
-/

import EvmAsm.Evm64.EvmWord

theorem BitVec.and_two_pow_sub_one_eq_zero_iff
    (v : BitVec 64) (k : Nat) (hk : k ≤ 64) :
    v &&& BitVec.ofNat 64 (2 ^ k - 1) = 0#64 ↔ 2 ^ k ∣ v.toNat := by
  have hpow : 2 ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hk
  have hlt : 2 ^ k - 1 < 2 ^ 64 := by omega
  have hmask : (BitVec.ofNat 64 (2 ^ k - 1)).toNat = 2 ^ k - 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hzero : (0#64 : BitVec 64).toNat = 0 := by
    rw [BitVec.toNat_ofNat]
  rw [← BitVec.toNat_inj, hzero, BitVec.toNat_and, hmask,
    Nat.and_two_pow_sub_one_eq_mod, Nat.dvd_iff_mod_eq_zero]

#print axioms BitVec.and_two_pow_sub_one_eq_zero_iff
