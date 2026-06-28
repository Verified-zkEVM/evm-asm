/-
  EvmAsm.EL.Withdrawal

  Pure decode spec for an EIP-4895 consensus-layer withdrawal — the coincidence target the verified
  `withdrawal_decode` drop-in (T2 of #9373) is proven equal to. A withdrawal is RLP-encoded as a
  4-element list `[index, validator_index, address, amount]`:

    - `index`           : u64 scalar (RLP uint)
    - `validatorIndex`  : u64 scalar (RLP uint)
    - `address`         : 20-byte bytestring, decoded to a 160-bit word
    - `amount`          : u64 scalar (RLP uint, in gwei)

  `decodeWithdrawal` decodes the *whole* input (no trailing bytes) as such a list, reading the three
  scalar fields big-endian and requiring the address be exactly 20 bytes; any structural deviation
  (wrong element count, a nested list where bytes are expected, a non-20-byte address, trailing
  bytes) yields `none`. The numeric fields coincide with `decodeScalar` of each list element. The
  address is kept as a `BitVec 160` (big-endian value of the 20 bytes), mirroring how u256 scalars
  are modelled as `BitVec`s elsewhere.
-/

import EvmAsm.EL.RLP.FullDecode
import EvmAsm.EL.RLP.Scalar

namespace EvmAsm.EL

open EvmAsm.EL.RLP

/-- A decoded EIP-4895 withdrawal. Scalars are kept as `Nat` (the big-endian value); the address is
    a `BitVec 160` (the big-endian value of the 20 address bytes). -/
structure Withdrawal where
  index : Nat
  validatorIndex : Nat
  address : BitVec 160
  amount : Nat
  deriving DecidableEq, Repr

/-- Decode the full RLP encoding of an EIP-4895 withdrawal: a 4-element list whose elements are
    `[index, validator_index, address (20 bytes), amount]`. Returns `none` on any structural
    deviation or trailing bytes.

    **Strict** (consensus-canonical): the three scalar fields (`index`, `validator_index`,
    `amount`) must be canonical minimal big-endian `uint64` encodings — no leading zero byte
    (`d.headD 1 ≠ 0`, matching `decodeScalar` / execution-specs `_deserialize_to_uint`) and at
    most 8 bytes (the value fits `u64`). A non-canonical scalar (e.g. `0x0005`, the bare `0x00`,
    or a 9+-byte value) yields `none`. The address (element 2) must be exactly 20 bytes. -/
def decodeWithdrawal (bs : List Byte) : Option Withdrawal :=
  match decodeFully bs with
  | some (.list [.bytes d0, .bytes d1, .bytes d2, .bytes d3]) =>
      if d0.headD 1 ≠ 0 ∧ d0.length ≤ 8 ∧ d1.headD 1 ≠ 0 ∧ d1.length ≤ 8
         ∧ d2.length = 20 ∧ d3.headD 1 ≠ 0 ∧ d3.length ≤ 8 then
        some { index := Nat.fromBytesBE d0,
               validatorIndex := Nat.fromBytesBE d1,
               address := BitVec.ofNat 160 (Nat.fromBytesBE d2),
               amount := Nat.fromBytesBE d3 }
      else none
  | _ => none

/-- `decodeWithdrawal` succeeds exactly when the input fully decodes to a 4-element byte-list whose
    three scalar elements are canonical minimal big-endian `uint64`s (no leading zero, `≤ 8`
    bytes) and whose address element is exactly 20 bytes; in that case the fields are the
    big-endian scalars / raw address of the elements. The defining unfolding, stated for the
    verified drop-in's coincidence proof. -/
theorem decodeWithdrawal_eq_some_iff (bs : List Byte) (w : Withdrawal) :
    decodeWithdrawal bs = some w ↔
      ∃ d0 d1 d2 d3 : List Byte,
        decodeFully bs = some (.list [.bytes d0, .bytes d1, .bytes d2, .bytes d3])
        ∧ d0.headD 1 ≠ 0 ∧ d0.length ≤ 8
        ∧ d1.headD 1 ≠ 0 ∧ d1.length ≤ 8
        ∧ d2.length = 20
        ∧ d3.headD 1 ≠ 0 ∧ d3.length ≤ 8
        ∧ w.index = Nat.fromBytesBE d0
        ∧ w.validatorIndex = Nat.fromBytesBE d1
        ∧ w.address = BitVec.ofNat 160 (Nat.fromBytesBE d2)
        ∧ w.amount = Nat.fromBytesBE d3 := by
  constructor
  · intro h
    unfold decodeWithdrawal at h
    split at h
    · -- the matching arm: `decodeFully bs = some (.list [4 bytes])`
      rename_i d0 d1 d2 d3 heq
      split at h
      · rename_i hcond
        obtain ⟨hc0, hl0, hc1, hl1, h20, hc3, hl3⟩ := hcond
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨d0, d1, d2, d3, heq, hc0, hl0, hc1, hl1, h20, hc3, hl3, rfl, rfl, rfl, rfl⟩
      · simp at h
    · simp at h
  · rintro ⟨d0, d1, d2, d3, hf, hc0, hl0, hc1, hl1, h20, hc3, hl3, hi, hv, ha, hamt⟩
    unfold decodeWithdrawal
    cases w
    subst hi hv ha hamt
    rw [hf]
    simp only [hc0, hl0, hc1, hl1, h20, hc3, hl3, ne_eq, not_false_eq_true, and_self, if_true]

end EvmAsm.EL
