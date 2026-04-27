/-
  EvmAsm.EL.RLP.Properties

  Round-trip correctness: `decode (encode item) = some (item, [])`.
-/
-- `Decode` transitively imports `Basic`.
import EvmAsm.EL.RLP.Decode

namespace EvmAsm.EL.RLP

/-! ## Nat.toBytesBE / fromBytesBE properties -/

theorem Nat.toBytesBE_zero : Nat.toBytesBE 0 = [] := by
  simp [Nat.toBytesBE]

theorem Nat.fromBytesBE_nil : Nat.fromBytesBE [] = 0 := by
  simp [Nat.fromBytesBE]

/-! ## takeBytes properties -/

/-- Taking 0 bytes always succeeds with an empty prefix and the original list. -/
theorem takeBytes_zero (bs : List Byte) :
    takeBytes bs 0 = some ([], bs) := by
  simp [takeBytes]

/-- Taking more bytes than the list contains returns `none`. -/
theorem takeBytes_length_lt {bs : List Byte} {n : Nat} (h : bs.length < n) :
    takeBytes bs n = none := by
  simp [takeBytes, Nat.not_le_of_lt h]

/-- When the list is at least `n` bytes long, `takeBytes` returns the obvious split. -/
theorem takeBytes_length_ge {bs : List Byte} {n : Nat} (h : n ≤ bs.length) :
    takeBytes bs n = some (bs.take n, bs.drop n) := by
  simp [takeBytes, h]

/-! ## readLength properties -/

/-- Reading zero length-bytes always succeeds with length 0 and the input
    list unchanged. -/
theorem readLength_zero (bs : List Byte) :
    readLength bs 0 = some (0, bs) := by
  simp [readLength, takeBytes]

/-- Reading more length-bytes than the input contains returns `none`. -/
theorem readLength_length_lt {bs : List Byte} {n : Nat} (h : bs.length < n) :
    readLength bs n = none := by
  simp [readLength, takeBytes, Nat.not_le_of_lt h]

/-! ## decodeAux trivial cases -/

/-- `decodeAux 0` always returns `none` (no fuel). -/
theorem decodeAux_zero_fuel (bs : List Byte) :
    decodeAux 0 bs = none := by
  simp [decodeAux]

/-- `decodeAux` on an empty stream returns `none` regardless of fuel. -/
theorem decodeAux_nil (fuel : Nat) :
    decodeAux fuel [] = none := by
  cases fuel <;> simp [decodeAux]

/-- Single-byte items: when the prefix `p` satisfies `p < 0x80`, `decodeAux`
    succeeds and returns `(.bytes [p], rest)` consuming one byte. -/
theorem decodeAux_single_byte (fuel : Nat) (pfx : Byte) (rest : List Byte)
    (h : pfx.toNat < 0x80) :
    decodeAux (fuel + 1) (pfx :: rest) = some (.bytes [pfx], rest) := by
  simp [decodeAux, h]

/-- Empty short byte string (prefix `0x80`): `decodeAux` returns `(.bytes [], rest)`
    consuming only the prefix byte. -/
theorem decodeAux_empty_string (fuel : Nat) (rest : List Byte) :
    decodeAux (fuel + 1) ((0x80 : Byte) :: rest) = some (.bytes [], rest) := by
  simp [decodeAux, takeBytes]

/-- Empty list (prefix `0xC0`): `decodeAux` returns `(.list [], rest)`
    consuming exactly the prefix byte. The short-list branch fires with
    `len = 0`, so `takeBytes rest 0 = some ([], rest)` and the recursive
    `decodeItems fuel []` returns `some ([], [])` which has empty
    leftover. -/
theorem decodeAux_empty_list (fuel : Nat) (rest : List Byte) :
    decodeAux (fuel + 1) ((0xC0 : Byte) :: rest) = some (.list [], rest) := by
  simp [decodeAux, takeBytes, decodeItems]

/-- Two-byte short string (prefix `0x82`): `decodeAux` returns
    `(.bytes [b1, b2], rest)` consuming three bytes (prefix + 2 payload).
    The two-byte payload is multi-byte, so the canonical-form check
    (which only fires for single-byte strings) is bypassed. -/
theorem decodeAux_two_byte_string (fuel : Nat) (b1 b2 : Byte) (rest : List Byte) :
    decodeAux (fuel + 1) ((0x82 : Byte) :: b1 :: b2 :: rest) =
      some (.bytes [b1, b2], rest) := by
  simp [decodeAux, takeBytes]

/-- Three-byte short string (prefix `0x83`): `decodeAux` returns
    `(.bytes [b1, b2, b3], rest)` consuming four bytes (prefix + 3
    payload). Multi-byte payload bypasses the canonical-form check. -/
theorem decodeAux_three_byte_string
    (fuel : Nat) (b1 b2 b3 : Byte) (rest : List Byte) :
    decodeAux (fuel + 1) ((0x83 : Byte) :: b1 :: b2 :: b3 :: rest) =
      some (.bytes [b1, b2, b3], rest) := by
  simp [decodeAux, takeBytes]

/-- Four-byte short string (prefix `0x84`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_four_byte_string
    (fuel : Nat) (b1 b2 b3 b4 : Byte) (rest : List Byte) :
    decodeAux (fuel + 1) ((0x84 : Byte) :: b1 :: b2 :: b3 :: b4 :: rest) =
      some (.bytes [b1, b2, b3, b4], rest) := by
  simp [decodeAux, takeBytes]

/-- Five-byte short string (prefix `0x85`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_five_byte_string
    (fuel : Nat) (b1 b2 b3 b4 b5 : Byte) (rest : List Byte) :
    decodeAux (fuel + 1) ((0x85 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: rest) =
      some (.bytes [b1, b2, b3, b4, b5], rest) := by
  simp [decodeAux, takeBytes]

/-! ## decode (top-level wrapper) trivial cases -/

/-- `decode []` returns `none` because `decodeAux 0 []` returns `none`. -/
theorem decode_nil : decode ([] : List Byte) = none := by
  simp [decode, decodeAux]

/-- `decode [pfx]` returns `(.bytes [pfx], [])` whenever `pfx < 0x80`.
    Specializes `decodeAux_single_byte` at the top-level fuel. -/
theorem decode_single_byte (pfx : Byte) (h : pfx.toNat < 0x80) :
    decode [pfx] = some (.bytes [pfx], []) := by
  simp [decode, decodeAux, h]

/-- `decode [0x80] = some (.bytes [], [])` — the canonical empty-string
    encoding. Specializes `decodeAux_empty_string` at the top-level fuel. -/
theorem decode_empty_string : decode [(0x80 : Byte)] = some (.bytes [], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xC0] = some (.list [], [])` — the canonical empty-list
    encoding. Specializes `decodeAux_empty_list` at the top-level fuel. -/
theorem decode_empty_list : decode [(0xC0 : Byte)] = some (.list [], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems]

/-- `decode [0x82, b1, b2] = some (.bytes [b1, b2], [])` — the canonical
    two-byte short-string encoding. Specializes `decodeAux_two_byte_string`
    at the top-level fuel. -/
theorem decode_two_byte_string (b1 b2 : Byte) :
    decode [(0x82 : Byte), b1, b2] = some (.bytes [b1, b2], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x83, b1, b2, b3] = some (.bytes [b1, b2, b3], [])` — the
    canonical three-byte short-string encoding. Specializes
    `decodeAux_three_byte_string` at the top-level fuel. -/
theorem decode_three_byte_string (b1 b2 b3 : Byte) :
    decode [(0x83 : Byte), b1, b2, b3] = some (.bytes [b1, b2, b3], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x84, b1, b2, b3, b4] = some (.bytes [b1, b2, b3, b4], [])`
    — the canonical four-byte short-string encoding. Specializes
    `decodeAux_four_byte_string` at the top-level fuel. -/
theorem decode_four_byte_string (b1 b2 b3 b4 : Byte) :
    decode [(0x84 : Byte), b1, b2, b3, b4] =
      some (.bytes [b1, b2, b3, b4], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x85, b1, b2, b3, b4, b5] = some (.bytes [b1..b5], [])`
    — the canonical five-byte short-string encoding. -/
theorem decode_five_byte_string (b1 b2 b3 b4 b5 : Byte) :
    decode [(0x85 : Byte), b1, b2, b3, b4, b5] =
      some (.bytes [b1, b2, b3, b4, b5], []) := by
  simp [decode, decodeAux, takeBytes]

/-! ## encodeBytes characterizations -/

/-- Empty byte string encodes to the single prefix `[0x80]`. -/
theorem encodeBytes_nil : encodeBytes [] = [BitVec.ofNat 8 0x80] := by
  simp [encodeBytes]

/-- Single small byte (`b < 0x80`): the byte is its own encoding. -/
theorem encodeBytes_single_small (b : Byte) (h : b.toNat < 0x80) :
    encodeBytes [b] = [b] := by
  simp [encodeBytes, h]

/-- Single large byte (`b ≥ 0x80`): encoded as `[0x81, b]`. -/
theorem encodeBytes_single_large (b : Byte) (h : ¬ b.toNat < 0x80) :
    encodeBytes [b] = [BitVec.ofNat 8 0x81, b] := by
  simp [encodeBytes, h]

/-- Two-byte short string: `encodeBytes [a, b] = [0x82, a, b]`.
    No canonical-form branching applies; `data.length = 2 > 1` skips
    the single-byte path, and `2 ≤ 55` selects the short-string form. -/
theorem encodeBytes_pair (a b : Byte) :
    encodeBytes [a, b] = [BitVec.ofNat 8 0x82, a, b] := by
  simp [encodeBytes]

/-- Three-byte short string: `encodeBytes [a, b, c] = [0x83, a, b, c]`. -/
theorem encodeBytes_triple (a b c : Byte) :
    encodeBytes [a, b, c] = [BitVec.ofNat 8 0x83, a, b, c] := by
  simp [encodeBytes]

/-- Four-byte short string: `encodeBytes [a, b, c, d] = [0x84, a, b, c, d]`. -/
theorem encodeBytes_quad (a b c d : Byte) :
    encodeBytes [a, b, c, d] = [BitVec.ofNat 8 0x84, a, b, c, d] := by
  simp [encodeBytes]

/-! ## Encoding produces non-empty output -/

theorem encodeBytes_nonempty (data : List Byte) :
    (encodeBytes data).length > 0 := by
  simp [encodeBytes]
  split
  · split <;> simp
  · split <;> simp [List.length_append]

theorem encode_nonempty (item : RLPItem) : (encode item).length > 0 := by
  cases item with
  | bytes data => exact encodeBytes_nonempty data
  | list items =>
    simp [encode]
    split <;> simp [List.length_append]

/-! ## Round-trip correctness (parametric cases)

These lemmas prove `decode (encode (.bytes [b])) = some (.bytes [b], [])`
mechanically (not via `decide`) by chaining the existing `encodeBytes_*`
and `decode_*` characterizations. They cover the single-byte cases
across all values of `b` — useful as building blocks for an eventual
fully parametric round-trip theorem. -/

/-- Single-byte round-trip for small bytes (`b < 0x80`): the byte is
    its own encoding, and the decoder maps it back to `.bytes [b]`. -/
theorem decode_encode_bytes_single_small (b : Byte) (h : b.toNat < 0x80) :
    decode (encode (.bytes [b])) = some (.bytes [b], []) := by
  simp only [encode, encodeBytes_single_small _ h, decode_single_byte _ h]

/-- Empty byte string round-trip:
    `decode (encode (.bytes [])) = some (.bytes [], [])`. Chains
    `encodeBytes_nil` with `decode_empty_string`. -/
theorem decode_encode_bytes_empty :
    decode (encode (.bytes [])) = some (.bytes [], []) := by
  simp only [encode, encodeBytes_nil]
  exact decode_empty_string

/-! ## Round-trip correctness (concrete cases)

The round-trip property `decode (encode item) = some (item, [])` is verified
computationally via `decide` on representative test cases covering
all encoding forms:
- Single byte (value < 0x80)
- Short byte string (0-55 bytes)
- Short list (payload 0-55 bytes)
- Nested lists
- Canonical form rejection
-/

-- Single bytes
example : decode (encode (.bytes [0x00])) = some (.bytes [0x00], []) := by decide
example : decode (encode (.bytes [0x0F])) = some (.bytes [0x0F], []) := by decide
example : decode (encode (.bytes [0x7F])) = some (.bytes [0x7F], []) := by decide

-- Short byte strings
example : decode (encode (.bytes [])) = some (.bytes [], []) := by decide
example : decode (encode (.bytes [0x80])) = some (.bytes [0x80], []) := by decide
example : decode (encode (.bytes [0xFF])) = some (.bytes [0xFF], []) := by decide
example : decode (encode (.bytes [0x64, 0x6F, 0x67])) =
    some (.bytes [0x64, 0x6F, 0x67], []) := by decide

-- Lists
example : decode (encode (.list [])) = some (.list [], []) := by decide
example : decode (encode (.list [.bytes []])) = some (.list [.bytes []], []) := by
  decide
example : decode (encode (.list [.bytes [0x01], .bytes [0x02]])) =
    some (.list [.bytes [0x01], .bytes [0x02]], []) := by decide

-- Nested lists
example : decode (encode (.list [.list []])) = some (.list [.list []], []) := by
  decide
example : decode (encode (.list [.list [], .list []])) =
    some (.list [.list [], .list []], []) := by decide
example : decode (encode (.list [.list [.list []]])) =
    some (.list [.list [.list []]], []) := by decide

-- Encoding matches RLP specification
example : encode (.bytes []) = [0x80] := by decide
example : encode (.list []) = [0xC0] := by decide
example : encode (.bytes [0x0F]) = [0x0F] := by decide
example : encode (.bytes [0x80]) = [0x81, 0x80] := by decide
example : encode (.bytes [0x64, 0x6F, 0x67]) = [0x83, 0x64, 0x6F, 0x67] := by
  decide

-- Canonical form: non-canonical encodings are rejected
example : decode [0x81, 0x0F] = none := by decide
example : decode [0x81, 0x7F] = none := by decide
example : decode [0x81, 0x00] = none := by decide

end EvmAsm.EL.RLP
