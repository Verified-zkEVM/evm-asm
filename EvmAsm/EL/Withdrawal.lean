/-
  EvmAsm.EL.Withdrawal

  Pure decode spec for an EIP-4895 consensus-layer withdrawal — the coincidence target the verified
  `withdrawal_decode` drop-in (T2 of #9373) is proven equal to. A withdrawal is RLP-encoded as a
  4-element list `[index, validator_index, address, amount]`:

    - `index`           : u64 scalar (RLP uint)
    - `validatorIndex`  : u64 scalar (RLP uint)
    - `address`         : 20-byte bytestring
    - `amount`          : u64 scalar (RLP uint, in gwei)

  `decodeWithdrawal` decodes the *whole* input (no trailing bytes) as such a list, reading the three
  scalar fields big-endian and requiring the address be exactly 20 bytes; any structural deviation
  (wrong element count, a nested list where bytes are expected, a non-20-byte address, trailing
  bytes) yields `none`. The numeric fields coincide with `decodeScalar` of each list element.
-/

import EvmAsm.EL.RLP.FullDecode
import EvmAsm.EL.RLP.Scalar

namespace EvmAsm.EL

open EvmAsm.EL.RLP

/-- A decoded EIP-4895 withdrawal. Scalars are kept as `Nat` (the big-endian value); the address is
    the raw 20-byte string. -/
structure Withdrawal where
  index : Nat
  validatorIndex : Nat
  address : List Byte
  amount : Nat
  deriving DecidableEq, Repr

/-- Decode the full RLP encoding of an EIP-4895 withdrawal: a 4-element list whose elements are
    `[index, validator_index, address (20 bytes), amount]`. Returns `none` on any structural
    deviation or trailing bytes. -/
def decodeWithdrawal (bs : List Byte) : Option Withdrawal :=
  match decodeFully bs with
  | some (.list [.bytes d0, .bytes d1, .bytes d2, .bytes d3]) =>
      if d2.length = 20 then
        some { index := Nat.fromBytesBE d0,
               validatorIndex := Nat.fromBytesBE d1,
               address := d2,
               amount := Nat.fromBytesBE d3 }
      else none
  | _ => none

/-- `decodeWithdrawal` succeeds exactly when the input fully decodes to a 4-element byte-list with a
    20-byte address; in that case the fields are the big-endian scalars / raw address of the
    elements. The defining unfolding, stated for the verified drop-in's coincidence proof. -/
theorem decodeWithdrawal_eq_some_iff (bs : List Byte) (w : Withdrawal) :
    decodeWithdrawal bs = some w ↔
      ∃ d0 d1 d3 : List Byte,
        decodeFully bs = some (.list [.bytes d0, .bytes d1, .bytes w.address, .bytes d3])
        ∧ w.address.length = 20
        ∧ w.index = Nat.fromBytesBE d0
        ∧ w.validatorIndex = Nat.fromBytesBE d1
        ∧ w.amount = Nat.fromBytesBE d3 := by
  constructor
  · intro h
    unfold decodeWithdrawal at h
    split at h
    · -- the matching arm: `decodeFully bs = some (.list [4 bytes])`
      rename_i d0 d1 d2 d3 heq
      split at h
      · rename_i h20
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨d0, d1, d3, heq, h20, rfl, rfl, rfl⟩
      · simp at h
    · simp at h
  · rintro ⟨d0, d1, d3, hf, h20, hi, hv, ha⟩
    unfold decodeWithdrawal
    cases w
    subst hi hv ha
    rw [hf]
    simp [h20]

end EvmAsm.EL
