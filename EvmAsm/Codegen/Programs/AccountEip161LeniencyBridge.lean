/-
  EvmAsm.Codegen.Programs.AccountEip161LeniencyBridge

  #11346, item 2: the guest's **lenient** EIP-161 zero test agrees with the
  reference's, and the agreement is proved rather than observed.

  The guest tests a nonce/balance field for zero by accumulating its content
  bytes big-endian and comparing to `0` (`beAccum_eq_zero_iff`), which accepts
  non-canonical encodings — `0x00`, `0x00 0x00`, and the empty field all read as
  zero.  The reference reads the same field with `bytesBEtoNat`.  Whether those
  two leniencies coincide was documented as a coincidence; `Nat.fromBytesBE_eq_zero_iff`
  makes it a theorem, and this module consumes it.

  The EIP-161 leniency proof now consumes the shared `AccountDecodeSpec.beAccum`
  model directly, so the same accumulator semantics and `fromBytesBE` theorem
  serve both account-decoding callers.
-/

import EvmAsm.Codegen.Programs.AccountIsEip161EmptySpec

namespace EvmAsm.Codegen.AccountIsEip161EmptySpec

open EvmAsm.Rv64 EvmAsm.EL.RLP

/-- ⭐ **The leniency agreement.**  The guest's "every content byte is zero"
    test and the reference's `Nat.fromBytesBE … = 0` are the same predicate on
    the same field — so the guest's tolerance of non-canonical zero encodings is
    matched by the reference, not merely unpunished by it. -/
theorem leniency_agrees (bs : List (BitVec 8)) (off n : Nat) (fld : List (BitVec 8))
    (hbound : off + n ≤ bs.length)
    (hcontent : (bs.drop off).take n = fld) :
    (∀ k, k < n → bs.getD (off + k) 0 = 0) ↔ Nat.fromBytesBE fld = 0 := by
  rw [Nat.fromBytesBE_eq_zero_iff]
  have hlen : fld.length = n := by
    rw [← hcontent, List.length_take, List.length_drop]; omega
  -- index `i` of the content slice is absolute index `off + i` of the buffer
  have hget : ∀ i, i < n → fld.getD i 0 = bs.getD (off + i) 0 := by
    intro i hi
    rw [← hcontent]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hi]
  have hgetD : ∀ (i : Nat) (hi : i < fld.length), fld.getD i 0 = fld[i] := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl
  constructor
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [← hgetD i hi, hget i (by omega)]
    exact h i (by omega)
  · intro h k hk
    rw [← hget k hk, hgetD k (by omega)]
    exact h _ (List.getElem_mem _)

end EvmAsm.Codegen.AccountIsEip161EmptySpec
