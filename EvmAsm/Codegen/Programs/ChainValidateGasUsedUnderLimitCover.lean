/-
  Anti-vacuity cover for `chain_validate_gas_used_under_limit_spec_within`
  (#12471 / #12479 file-size split).
-/

import EvmAsm.Codegen.Programs.ChainValidateGasUsedUnderLimitLoopClose

namespace EvmAsm.Codegen.ChainValidateGasUsedUnderLimitSpec

open EvmAsm.Rv64
open EvmAsm.Codegen.ChainValidateExtraDataLengthSpec (hdrOff hdrBaseAt)

/-! ## Anti-vacuity cover (#12471)

    The old `hAllSlack` (`lengths[i]! + 9 ≤ drop.length`) was unsatisfiable on every
    exact-fit nonempty blob (last index forces `L+9 ≤ L`). The repaired premise
    *set* of `chain_validate_gas_used_under_limit_spec_within` is jointly inhabited
    on an exact-fit nonempty 8-aligned blob — the case the old premise excluded. -/

/-- Exact-fit nonempty cover: `lengths = [48, 48]`, `|bigBytes| = 96`, `hdrBase = MEM_START`.
    Lengths are 8-aligned so `hAllAlign`/`hAllSalign` hold (unlike `[50,50]`). -/
example :
    let lengths := [48, 48]
    let bigBytes : List (BitVec 8) := List.replicate 96 (0 : BitVec 8)
    let hdrBase : Word := BitVec.ofNat 64 MEM_START
    (∀ i, i < lengths.length → hdrOff lengths i % 8 = 0) ∧
    (∀ i, i < lengths.length → hdrOff lengths i ≤ bigBytes.length) ∧
    (∀ i, i < lengths.length → (hdrBaseAt hdrBase lengths i).toNat % 8 = 0) ∧
    (∀ i, i < lengths.length →
      lengths[i]! ≤ (bigBytes.drop (hdrOff lengths i)).length) ∧
    (∀ i, i < lengths.length →
      (hdrBaseAt hdrBase lengths i).toNat + lengths[i]! + 9 < 2 ^ 64) ∧
    (∀ i, i < lengths.length →
      (hdrBaseAt hdrBase lengths i).toNat + (bigBytes.drop (hdrOff lengths i)).length <
        2 ^ 64) ∧
    (∀ i, i < lengths.length → 0 < (bigBytes.drop (hdrOff lengths i)).length) ∧
    (∀ i, i < lengths.length → ∀ k, k < (bigBytes.drop (hdrOff lengths i)).length →
      isValidByteAccess (hdrBaseAt hdrBase lengths i + BitVec.ofNat 64 k) = true) := by
  -- Discharge each binder of the repaired set on this concrete exact-fit witness.
  refine ⟨?hAllAlign, ?hAllLen, ?hAllSalign, ?hAllBytes, ?hAllNowrap, ?hAllOver, ?hAllNz,
    ?hAllValid⟩
  · intro i hi; match i with
    | 0 => decide
    | 1 => decide
    | n + 2 => cases (Nat.not_lt_of_le (by omega : 2 ≤ n + 2) hi)
  · intro i hi; match i with
    | 0 => decide
    | 1 => decide
    | n + 2 => cases (Nat.not_lt_of_le (by omega : 2 ≤ n + 2) hi)
  · intro i hi; match i with
    | 0 => decide
    | 1 => decide
    | n + 2 => cases (Nat.not_lt_of_le (by omega : 2 ≤ n + 2) hi)
  · intro i hi; match i with
    | 0 => decide
    | 1 => decide
    | n + 2 => cases (Nat.not_lt_of_le (by omega : 2 ≤ n + 2) hi)
  · intro i hi; match i with
    | 0 => decide
    | 1 => decide
    | n + 2 => cases (Nat.not_lt_of_le (by omega : 2 ≤ n + 2) hi)
  · intro i hi; match i with
    | 0 => decide
    | 1 => decide
    | n + 2 => cases (Nat.not_lt_of_le (by omega : 2 ≤ n + 2) hi)
  · intro i hi; match i with
    | 0 => decide
    | 1 => decide
    | n + 2 => cases (Nat.not_lt_of_le (by omega : 2 ≤ n + 2) hi)
  · intro i hi k hk
    match i with
    | 0 =>
      have hk96 : k < 96 := by
        simpa [hdrOff] using hk
      have hsum :
          (hdrBaseAt (BitVec.ofNat 64 MEM_START) [48, 48] 0 + BitVec.ofNat 64 k).toNat =
            32 + k := by
        simp only [hdrBaseAt, hdrOff, List.take_zero, List.sum_nil, MEM_START]
        rw [BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega : 32 < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : 32 + k < 2 ^ 64)]
      simp only [isValidByteAccess, isValidMemAddr, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq]
      refine Or.inl (Or.inl ?_)
      constructor
      · rw [hsum]; change 32 ≤ 32 + k; omega
      · rw [hsum]; change 32 + k ≤ 0x78000000; omega
    | 1 =>
      have hk48 : k < 48 := by
        simpa [hdrOff] using hk
      have hsum :
          (hdrBaseAt (BitVec.ofNat 64 MEM_START) [48, 48] 1 + BitVec.ofNat 64 k).toNat =
            80 + k := by
        simp only [hdrBaseAt, hdrOff, MEM_START]
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        simp only [List.take, List.sum_cons, List.sum_nil, Nat.add_zero]
        have hk64 : k < 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt (by omega : 32 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 48 < 2 ^ 64)]
        change (80 % 2 ^ 64 + (BitVec.ofNat 64 k).toNat) % 2 ^ 64 = 80 + k
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 80 < 2 ^ 64), Nat.mod_eq_of_lt hk64,
          Nat.mod_eq_of_lt (by omega : 80 + k < 2 ^ 64)]
      simp only [isValidByteAccess, isValidMemAddr, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq]
      refine Or.inl (Or.inl ?_)
      constructor
      · rw [hsum]; change 32 ≤ 80 + k; omega
      · rw [hsum]; change 80 + k ≤ 0x78000000; omega
    | n + 2 => cases (Nat.not_lt_of_le (by omega : 2 ≤ n + 2) hi)

end EvmAsm.Codegen.ChainValidateGasUsedUnderLimitSpec
