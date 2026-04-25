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
