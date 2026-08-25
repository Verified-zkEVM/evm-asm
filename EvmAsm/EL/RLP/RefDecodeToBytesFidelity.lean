/-
  EvmAsm.EL.RLP.RefDecodeToBytesFidelity

  **Port-fidelity clause table for `decode_to_bytes`** (`ethereum-rlp` 0.1.6,
  `rlp.py:387-424`), the one reference function in the RLP correspondence map
  with no named row (#12843 §1).

  `EL.RLP.Ref.decodeToBytes` (`RefDecode.lean:110`) is a clause-for-clause port,
  but three of its clauses are **not syntactic restatements** of the Python, and
  a `.ported` correspondence row may only be claimed once those are proved
  rather than read.  Each is proved here, each against the shape the Python
  actually writes.

  | # | `rlp.py` | port | syntactic? |
  |---|---|---|---|
  | 1 | `len(eb) == 1 and eb[0] < 0x80` | `bs.length = 1 ∧ p < 0x80` | yes |
  | 2 | `len_raw_data < 0` → "negative length" | `p < 0x80` hoisted before `lenRaw` | **no** — `negative_length_test_faithful` |
  | 3 | `len_raw_data >= len(eb)` → truncated | `lenRaw ≥ bs.length` | yes |
  | 4 | `1 + len_raw_data < len(eb)` → trailing | `1 + lenRaw < bs.length` | yes |
  | 5 | `len_raw_data == 1 and raw_data[0] < 0x80` | `lenRaw = 1 ∧ (raw.getD 0 0).toNat < 0x80` | yes |
  | 6 | `decoded_data_start_idx - 1 >= len(eb)` | `lenLen ≥ bs.length` | **no** — `long_trunc_test_faithful` |
  | 7 | `encoded_bytes[1] == 0` | `rest.getD 0 0 = 0` | yes |
  | 8 | `len_decoded_data < 0x38` | `lenVal < 0x38` | yes |
  | 9 | `decoded_data_end_idx - 1 >= len(eb)` | `lenLen + lenVal ≥ bs.length` | **no** — `long_end_test_faithful` |
  | 10 | `decoded_data_end_idx < len(eb)` | `1 + lenLen + lenVal < bs.length` | **no** — `long_trailing_test_faithful` |

  Why each of the four is non-syntactic:

  * Clause 2 — Python computes a **signed** `len_raw_data = eb[0] - 0x80` and
    rejects it for being negative.  `Nat` subtraction truncates at zero, so the
    port cannot express that test after the fact; it hoists the condition to
    `p < 0x80` *before* forming `lenRaw`.
  * Clauses 6, 9, 10 — Python names the two cursor positions
    `decoded_data_start_idx = 1 + eb[0] - 0xB7` and
    `decoded_data_end_idx = start + len_decoded_data`, then tests them shifted by
    one.  The port carries `lenLen` and `lenVal` directly, so each test is
    written without the `± 1`.

  Every theorem below states the **Python expression over `Int`** on one side —
  Python integers are unbounded and signed, which is exactly what makes these
  clauses non-syntactic — and the port's `Nat` expression on the other.  The
  range hypothesis on each is load-bearing, not decoration: `*_needs_range`
  exhibits a concrete point where the two sides disagree without it.
-/

import EvmAsm.EL.RLP.RefDecode

namespace EvmAsm.EL.RLP
namespace RefDecodeToBytesFidelity

/-! ### Clause 2 — the signed "negative length" test -/

/-- Python: `len_raw_data = encoded_bytes[0] - 0x80`, then
    `if len_raw_data < 0: raise DecodingError("negative length")`.
    Port: the guard `p < 0x80`, applied before `lenRaw` is formed.  Same test. -/
theorem negative_length_test_faithful (p : Nat) :
    ((p : Int) - 0x80 < 0) ↔ p < 0x80 := by omega

/-! ### Clauses 6, 9, 10 — the shifted cursor positions

    `decoded_data_start_idx = 1 + encoded_bytes[0] - 0xB7`, and this arm is
    reached only when `encoded_bytes[0] > 0xB7`, i.e. `≥ 0xB8`. -/

/-- Clause 6. Python: `decoded_data_start_idx - 1 >= len(encoded_bytes)`.
    Port: `lenLen ≥ bs.length`, where `lenLen = p - 0xB7`. -/
theorem long_trunc_test_faithful (p n : Nat) (hp : 0xB8 ≤ p) :
    ((1 + (p : Int) - 0xB7) - 1 ≥ (n : Int)) ↔ (p - 0xB7 ≥ n) := by
  omega

/-- Clause 9. Python: `decoded_data_end_idx - 1 >= len(encoded_bytes)`, where
    `decoded_data_end_idx = decoded_data_start_idx + len_decoded_data`.
    Port: `lenLen + lenVal ≥ bs.length`. -/
theorem long_end_test_faithful (p lenVal n : Nat) (hp : 0xB8 ≤ p) :
    (((1 + (p : Int) - 0xB7) + (lenVal : Int)) - 1 ≥ (n : Int))
      ↔ ((p - 0xB7) + lenVal ≥ n) := by
  omega

/-- Clause 10. Python: `decoded_data_end_idx < len(encoded_bytes)`.
    Port: `1 + lenLen + lenVal < bs.length`. -/
theorem long_trailing_test_faithful (p lenVal n : Nat) (hp : 0xB8 ≤ p) :
    (((1 + (p : Int) - 0xB7) + (lenVal : Int)) < (n : Int))
      ↔ (1 + (p - 0xB7) + lenVal < n) := by
  omega

/-! ### Negative controls

    Each range hypothesis above is a real restriction, not a premise that holds
    everywhere.  `Nat` subtraction truncating at zero is precisely what makes
    the two sides come apart below `0xB8`, so without the hypothesis these are
    not merely unproved — they are false. -/

/-- Clause 6's range hypothesis is load-bearing: at `p = 0`, `n = 0` the Python
    test is `-183 ≥ 0` (false) while the port's is `0 ≥ 0` (true). -/
theorem long_trunc_test_needs_range :
    ¬ (((1 + (0 : Int) - 0xB7) - 1 ≥ ((0 : Nat) : Int)) ↔ ((0 : Nat) - 0xB7 ≥ 0)) := by
  decide

/-- Clause 9's range hypothesis is load-bearing, same point. -/
theorem long_end_test_needs_range :
    ¬ ((((1 + (0 : Int) - 0xB7) + ((0 : Nat) : Int)) - 1 ≥ ((0 : Nat) : Int))
        ↔ (((0 : Nat) - 0xB7) + 0 ≥ 0)) := by
  decide

/-- Clause 10's range hypothesis is load-bearing: at `p = 0`, `lenVal = 0`,
    `n = 1` the Python test is `-182 < 1` (true) while the port's is
    `1 + 0 + 0 < 1` (false). -/
theorem long_trailing_test_needs_range :
    ¬ ((((1 + (0 : Int) - 0xB7) + ((0 : Nat) : Int)) < ((1 : Nat) : Int))
        ↔ (1 + ((0 : Nat) - 0xB7) + 0 < 1)) := by
  decide

end RefDecodeToBytesFidelity
end EvmAsm.EL.RLP
