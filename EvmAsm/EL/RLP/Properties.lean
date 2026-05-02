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

/-- Six-byte short string (prefix `0x86`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_six_byte_string
    (fuel : Nat) (b1 b2 b3 b4 b5 b6 : Byte) (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x86 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: rest) =
      some (.bytes [b1, b2, b3, b4, b5, b6], rest) := by
  simp [decodeAux, takeBytes]

/-- Seven-byte short string (prefix `0x87`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_seven_byte_string
    (fuel : Nat) (b1 b2 b3 b4 b5 b6 b7 : Byte) (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x87 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest) =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7], rest) := by
  simp [decodeAux, takeBytes]

/-- Eight-byte short string (prefix `0x88`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_eight_byte_string
    (fuel : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 : Byte) (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x88 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: rest) =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8], rest) := by
  simp [decodeAux, takeBytes]

/-- Nine-byte short string (prefix `0x89`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_nine_byte_string
    (fuel : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 b9 : Byte) (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x89 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: rest) =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9], rest) := by
  simp [decodeAux, takeBytes]

/-- Ten-byte short string (prefix `0x8A`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_ten_byte_string
    (fuel : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Byte) (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x8A : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 :: rest) =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10], rest) := by
  simp [decodeAux, takeBytes]

/-- Eleven-byte short string (prefix `0x8B`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_eleven_byte_string
    (fuel : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Byte) (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x8B : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: rest) =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11], rest) := by
  simp [decodeAux, takeBytes]

/-- Twelve-byte short string (prefix `0x8C`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_twelve_byte_string
    (fuel : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x8C : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: rest) =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12], rest) := by
  simp [decodeAux, takeBytes]

/-- Thirteen-byte short string (prefix `0x8D`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_thirteen_byte_string
    (fuel : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x8D : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: rest) =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13], rest) := by
  simp [decodeAux, takeBytes]

/-- Fourteen-byte short string (prefix `0x8E`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_fourteen_byte_string
    (fuel : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x8E : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: rest) =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Fifteen-byte short string (prefix `0x8F`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_fifteen_byte_string
    (fuel : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x8F : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: rest) =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Sixteen-byte short string (prefix `0x90`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_sixteen_byte_string
    (fuel : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x90 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Seventeen-byte short string (prefix `0x91`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_seventeen_byte_string
    (fuel : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x91 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Eighteen-byte short string (prefix `0x92`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_eighteen_byte_string
    (fuel : Nat) (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x92 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Nineteen-byte short string (prefix `0x93`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_nineteen_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x93 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Twenty-byte short string (prefix `0x94`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_twenty_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x94 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Twenty-one-byte short string (prefix `0x95`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_twenty_one_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x95 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Twenty-two-byte short string (prefix `0x96`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_twenty_two_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 :
      Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x96 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Twenty-three-byte short string (prefix `0x97`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_twenty_three_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x97 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Twenty-four-byte short string (prefix `0x98`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_twenty_four_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x98 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Twenty-five-byte short string (prefix `0x99`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_twenty_five_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x99 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Twenty-six-byte short string (prefix `0x9A`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_twenty_six_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x9A : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Twenty-seven-byte short string (prefix `0x9B`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_twenty_seven_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x9B : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Twenty-eight-byte short string (prefix `0x9C`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_twenty_eight_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x9C : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Twenty-nine-byte short string (prefix `0x9D`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_twenty_nine_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x9D : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Thirty-byte short string (prefix `0x9E`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_thirty_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x9E : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Thirty-one-byte short string (prefix `0x9F`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_thirty_one_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0x9F : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Thirty-two-byte short string (prefix `0xA0`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_thirty_two_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xA0 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Thirty-three-byte short string (prefix `0xA1`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_thirty_three_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xA1 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Thirty-four-byte short string (prefix `0xA2`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_thirty_four_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xA2 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Thirty-five-byte short string (prefix `0xA3`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_thirty_five_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xA3 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Thirty-six-byte short string (prefix `0xA4`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_thirty_six_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xA4 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Thirty-seven-byte short string (prefix `0xA5`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_thirty_seven_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xA5 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Thirty-eight-byte short string (prefix `0xA6`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_thirty_eight_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xA6 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Thirty-nine-byte short string (prefix `0xA7`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_thirty_nine_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xA7 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Forty-byte short string (prefix `0xA8`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_forty_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 :
      Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xA8 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Forty-one-byte short string (prefix `0xA9`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_forty_one_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 :
      Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xA9 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 :: b41 ::
          rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Forty-two-byte short string (prefix `0xAA`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_forty_two_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 :
      Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xAA : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 :: b41 ::
          b42 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Forty-three-byte short string (prefix `0xAB`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_forty_three_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xAB : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 :: b41 ::
          b42 :: b43 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Forty-four-byte short string (prefix `0xAC`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_forty_four_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xAC : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 :: b41 ::
          b42 :: b43 :: b44 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Forty-five-byte short string (prefix `0xAD`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_forty_five_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xAD : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 :: b41 ::
          b42 :: b43 :: b44 :: b45 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Forty-six-byte short string (prefix `0xAE`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_forty_six_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xAE : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 :: b41 ::
          b42 :: b43 :: b44 :: b45 :: b46 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Forty-seven-byte short string (prefix `0xAF`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_forty_seven_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xAF : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 :: b41 ::
          b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Forty-eight-byte short string (prefix `0xB0`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_forty_eight_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB0 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 :: b41 ::
          b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Canonical-form rejection: prefix `0x81` followed by a byte `b`
    with `b.toNat < 0x80` is non-canonical (the byte should have
    been encoded as itself, not under prefix `0x81`), so `decodeAux`
    returns `none`. -/
theorem decodeAux_canonical_rejection_single
    (fuel : Nat) (b : Byte) (rest : List Byte) (h : b.toNat < 0x80) :
    decodeAux (fuel + 1) ((0x81 : Byte) :: b :: rest) = none := by
  simp [decodeAux, takeBytes, h]

/-- Singleton list containing one small byte: top-level `decode` of
    `[0xC1, b]` with `b < 0x80` returns `.list [.bytes [b]]`. The
    short-list branch fires with payload length 1, the inner byte is
    recognized as a single-byte item, and the list closes cleanly. -/
theorem decode_singleton_list_small_byte (b : Byte) (h : b.toNat < 0x80) :
    decode [(0xC1 : Byte), b] = some (.list [.bytes [b]], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems, h]

/-- Singleton list containing the empty byte string:
    `decode [0xC1, 0x80] = some (.list [.bytes []], [])`. The
    short-list branch fires with payload length 1, the inner `0x80`
    is recognized as the empty short-string, and the list closes
    cleanly. -/
theorem decode_singleton_list_empty_string :
    decode [(0xC1 : Byte), (0x80 : Byte)] = some (.list [.bytes []], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems]

/-- Singleton list containing the empty list:
    `decode [0xC1, 0xC0] = some (.list [.list []], [])`. The
    short-list branch fires with payload length 1, the inner `0xC0`
    is recognized as the empty list, and the outer list closes. -/
theorem decode_singleton_list_empty_list :
    decode [(0xC1 : Byte), (0xC0 : Byte)] = some (.list [.list []], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems]

/-- Singleton list containing a single large byte: `decode [0xC2, 0x81, b]`
    with `b ≥ 0x80` returns `.list [.bytes [b]]`. The outer short-list
    branch fires with payload length 2, the inner `[0x81, b]` decodes
    as a single-byte short string (canonical form, since `b ≥ 0x80`),
    and the outer list closes. -/
theorem decode_singleton_list_large_byte (b : Byte) (h : ¬ b.toNat < 0x80) :
    decode [(0xC2 : Byte), (0x81 : Byte), b] =
      some (.list [.bytes [b]], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems, h]

/-- Two-element list of small bytes:
    `decode [0xC2, b1, b2] = some (.list [.bytes [b1], .bytes [b2]], [])`
    when both `b1, b2 < 0x80`. Short-list branch fires with payload
    length 2, two single-byte items decoded in sequence, then closes. -/
theorem decode_pair_list_small_bytes
    (b1 b2 : Byte) (h1 : b1.toNat < 0x80) (h2 : b2.toNat < 0x80) :
    decode [(0xC2 : Byte), b1, b2] =
      some (.list [.bytes [b1], .bytes [b2]], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems, h1, h2]

/-- Three-element list of small bytes:
    `decode [0xC3, b1, b2, b3] = some (.list [.bytes [b1], .bytes [b2], .bytes [b3]], [])`
    when all `b1, b2, b3 < 0x80`. Short-list branch fires with payload
    length 3, three single-byte items decoded in sequence, then closes. -/
theorem decode_triple_list_small_bytes
    (b1 b2 b3 : Byte)
    (h1 : b1.toNat < 0x80) (h2 : b2.toNat < 0x80) (h3 : b3.toNat < 0x80) :
    decode [(0xC3 : Byte), b1, b2, b3] =
      some (.list [.bytes [b1], .bytes [b2], .bytes [b3]], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems, h1, h2, h3]

/-- Four-element list of small bytes:
    `decode [0xC4, b1, b2, b3, b4] = some (.list [.bytes [b1], .bytes [b2], .bytes [b3], .bytes [b4]], [])`
    when all `b1, b2, b3, b4 < 0x80`. Short-list branch fires with
    payload length 4, four single-byte items decoded in sequence, then
    closes. -/
theorem decode_quad_list_small_bytes
    (b1 b2 b3 b4 : Byte)
    (h1 : b1.toNat < 0x80) (h2 : b2.toNat < 0x80)
    (h3 : b3.toNat < 0x80) (h4 : b4.toNat < 0x80) :
    decode [(0xC4 : Byte), b1, b2, b3, b4] =
      some (.list [.bytes [b1], .bytes [b2], .bytes [b3], .bytes [b4]], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems, h1, h2, h3, h4]

/-- Two-element list of empty lists:
    `decode [0xC2, 0xC0, 0xC0] = some (.list [.list [], .list []], [])`.
    The outer short-list branch fires with payload length 2, two empty
    inner lists are decoded in sequence, then the outer closes. -/
theorem decode_pair_list_empty_lists :
    decode [(0xC2 : Byte), (0xC0 : Byte), (0xC0 : Byte)] =
      some (.list [.list [], .list []], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems]

/-- Two-element list of empty byte strings:
    `decode [0xC2, 0x80, 0x80] = some (.list [.bytes [], .bytes []], [])`.
    The outer short-list branch fires with payload length 2, two empty
    inner byte strings are decoded in sequence, then the outer closes. -/
theorem decode_pair_list_empty_strings :
    decode [(0xC2 : Byte), (0x80 : Byte), (0x80 : Byte)] =
      some (.list [.bytes [], .bytes []], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems]

/-- Three-element list of empty lists:
    `decode [0xC3, 0xC0, 0xC0, 0xC0] = some (.list [.list [], .list [], .list []], [])`.
    The outer short-list branch fires with payload length 3, three empty
    inner lists are decoded in sequence, then the outer closes. -/
theorem decode_triple_list_empty_lists :
    decode [(0xC3 : Byte), (0xC0 : Byte), (0xC0 : Byte), (0xC0 : Byte)] =
      some (.list [.list [], .list [], .list []], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems]

/-- Three-element list of empty byte strings:
    `decode [0xC3, 0x80, 0x80, 0x80] = some (.list [.bytes [], .bytes [], .bytes []], [])`.
    The outer short-list branch fires with payload length 3, three empty
    inner byte strings are decoded in sequence, then the outer closes. -/
theorem decode_triple_list_empty_strings :
    decode [(0xC3 : Byte), (0x80 : Byte), (0x80 : Byte), (0x80 : Byte)] =
      some (.list [.bytes [], .bytes [], .bytes []], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems]

/-- Four-element list of empty lists:
    `decode [0xC4, 0xC0, 0xC0, 0xC0, 0xC0] = some (.list [.list [], .list [], .list [], .list []], [])`.
    The outer short-list branch fires with payload length 4, four empty
    inner lists are decoded in sequence, then the outer closes. -/
theorem decode_quad_list_empty_lists :
    decode [(0xC4 : Byte), (0xC0 : Byte), (0xC0 : Byte), (0xC0 : Byte), (0xC0 : Byte)] =
      some (.list [.list [], .list [], .list [], .list []], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems]

/-- Mixed-content two-element list: a small byte followed by an empty
    string. `decode [0xC2, b, 0x80] = some (.list [.bytes [b], .bytes []], [])`
    when `b < 0x80`. -/
theorem decode_pair_list_byte_then_empty_string
    (b : Byte) (h : b.toNat < 0x80) :
    decode [(0xC2 : Byte), b, (0x80 : Byte)] =
      some (.list [.bytes [b], .bytes []], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems, h]

/-- Mixed-content two-element list: an empty list followed by a small
    byte. `decode [0xC2, 0xC0, b] = some (.list [.list [], .bytes [b]], [])`
    when `b < 0x80`. -/
theorem decode_pair_list_empty_list_then_byte
    (b : Byte) (h : b.toNat < 0x80) :
    decode [(0xC2 : Byte), (0xC0 : Byte), b] =
      some (.list [.list [], .bytes [b]], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems, h]

/-- Mixed-content two-element list: a small byte followed by an empty
    list. `decode [0xC2, b, 0xC0] = some (.list [.bytes [b], .list []], [])`
    when `b < 0x80`. Companion to `decode_pair_list_empty_list_then_byte`
    in the reverse order. -/
theorem decode_pair_list_byte_then_empty_list
    (b : Byte) (h : b.toNat < 0x80) :
    decode [(0xC2 : Byte), b, (0xC0 : Byte)] =
      some (.list [.bytes [b], .list []], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems, h]

/-- Two-element list with one large byte and one small byte:
    `decode [0xC3, 0x81, b_large, b_small] = some (.list [.bytes [b_large], .bytes [b_small]], [])`
    when `b_large ≥ 0x80` and `b_small < 0x80`. The outer short-list
    branch fires with payload length 3, the inner large-byte string is
    decoded under canonical form (0x81 prefix), then the small-byte
    item, then the outer closes. -/
theorem decode_pair_list_large_then_small_byte
    (b_large b_small : Byte)
    (h_l : ¬ b_large.toNat < 0x80) (h_s : b_small.toNat < 0x80) :
    decode [(0xC3 : Byte), (0x81 : Byte), b_large, b_small] =
      some (.list [.bytes [b_large], .bytes [b_small]], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems, h_l, h_s]

/-- Two-element list with one small byte and one large byte
    (the mirror of `decode_pair_list_large_then_small_byte`):
    `decode [0xC3, b_small, 0x81, b_large] = some (.list [.bytes [b_small], .bytes [b_large]], [])`
    when `b_small < 0x80` and `b_large ≥ 0x80`. The outer short-list
    branch fires with payload length 3, the small-byte item is decoded
    first as a single-byte string, then the inner `[0x81, b_large]` is
    decoded as a one-byte short string under canonical form. -/
theorem decode_pair_list_small_then_large_byte
    (b_small b_large : Byte)
    (h_s : b_small.toNat < 0x80) (h_l : ¬ b_large.toNat < 0x80) :
    decode [(0xC3 : Byte), b_small, (0x81 : Byte), b_large] =
      some (.list [.bytes [b_small], .bytes [b_large]], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems, h_s, h_l]

/-- Singleton list containing a two-byte short string:
    `decode [0xC3, 0x82, b1, b2] = some (.list [.bytes [b1, b2]], [])`.
    The outer short-list branch fires with payload length 3, the inner
    `[0x82, b1, b2]` decodes as a two-byte short string, and the outer
    list closes. -/
theorem decode_singleton_list_two_byte_string (b1 b2 : Byte) :
    decode [(0xC3 : Byte), (0x82 : Byte), b1, b2] =
      some (.list [.bytes [b1, b2]], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems]

/-- Singleton list containing a three-byte short string:
    `decode [0xC4, 0x83, b1, b2, b3] = some (.list [.bytes [b1, b2, b3]], [])`.
    The outer short-list branch fires with payload length 4, the inner
    `[0x83, b1, b2, b3]` decodes as a three-byte short string. -/
theorem decode_singleton_list_three_byte_string (b1 b2 b3 : Byte) :
    decode [(0xC4 : Byte), (0x83 : Byte), b1, b2, b3] =
      some (.list [.bytes [b1, b2, b3]], []) := by
  simp [decode, decodeAux, takeBytes, decodeItems]

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

/-- Canonical-form rejection at the top level: `decode [0x81, b]`
    returns `none` whenever `b.toNat < 0x80`. Specializes
    `decodeAux_canonical_rejection_single`. -/
theorem decode_canonical_rejection_single (b : Byte) (h : b.toNat < 0x80) :
    decode [(0x81 : Byte), b] = none := by
  simp [decode, decodeAux, takeBytes, h]

/-- `decode [0x82, b1, b2] = some (.bytes [b1, b2], [])` — the canonical
    two-byte short-string encoding. -/
theorem decode_two_byte_string (b1 b2 : Byte) :
    decode [(0x82 : Byte), b1, b2] = some (.bytes [b1, b2], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x83, b1, b2, b3] = some (.bytes [b1, b2, b3], [])` — the
    canonical three-byte short-string encoding. -/
theorem decode_three_byte_string (b1 b2 b3 : Byte) :
    decode [(0x83 : Byte), b1, b2, b3] = some (.bytes [b1, b2, b3], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x84, b1, b2, b3, b4] = some (.bytes [b1, b2, b3, b4], [])`
    — the canonical four-byte short-string encoding. -/
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

/-- `decode [0x86, b1..b6] = some (.bytes [b1..b6], [])` — the
    canonical six-byte short-string encoding. -/
theorem decode_six_byte_string (b1 b2 b3 b4 b5 b6 : Byte) :
    decode [(0x86 : Byte), b1, b2, b3, b4, b5, b6] =
      some (.bytes [b1, b2, b3, b4, b5, b6], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x87, b1..b7] = some (.bytes [b1..b7], [])` — the
    canonical seven-byte short-string encoding. -/
theorem decode_seven_byte_string (b1 b2 b3 b4 b5 b6 b7 : Byte) :
    decode [(0x87 : Byte), b1, b2, b3, b4, b5, b6, b7] =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x88, b1..b8] = some (.bytes [b1..b8], [])` — the
    canonical eight-byte short-string encoding. -/
theorem decode_eight_byte_string (b1 b2 b3 b4 b5 b6 b7 b8 : Byte) :
    decode [(0x88 : Byte), b1, b2, b3, b4, b5, b6, b7, b8] =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x89, b1..b9] = some (.bytes [b1..b9], [])` — the
    canonical nine-byte short-string encoding. -/
theorem decode_nine_byte_string (b1 b2 b3 b4 b5 b6 b7 b8 b9 : Byte) :
    decode [(0x89 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9] =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x8A, b1..b10] = some (.bytes [b1..b10], [])` — the
    canonical ten-byte short-string encoding. -/
theorem decode_ten_byte_string (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Byte) :
    decode [(0x8A : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10] =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x8B, b1..b11] = some (.bytes [b1..b11], [])` — the
    canonical eleven-byte short-string encoding. -/
theorem decode_eleven_byte_string (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Byte) :
    decode [(0x8B : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11] =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x8C, b1..b12] = some (.bytes [b1..b12], [])` — the
    canonical twelve-byte short-string encoding. -/
theorem decode_twelve_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : Byte) :
    decode [(0x8C : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12] =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x8D, b1..b13] = some (.bytes [b1..b13], [])` — the
    canonical thirteen-byte short-string encoding. -/
theorem decode_thirteen_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Byte) :
    decode [(0x8D : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13] =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13], []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x8E, b1..b14] = some (.bytes [b1..b14], [])` — the
    canonical fourteen-byte short-string encoding. -/
theorem decode_fourteen_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : Byte) :
    decode [(0x8E : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14] =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x8F, b1..b15] = some (.bytes [b1..b15], [])` — the
    canonical fifteen-byte short-string encoding. -/
theorem decode_fifteen_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Byte) :
    decode [(0x8F : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15] =
      some (.bytes [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x90, b1..b16] = some (.bytes [b1..b16], [])` — the
    canonical sixteen-byte short-string encoding. -/
theorem decode_sixteen_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 : Byte) :
    decode [(0x90 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x91, b1..b17] = some (.bytes [b1..b17], [])` — the
    canonical seventeen-byte short-string encoding. -/
theorem decode_seventeen_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 : Byte) :
    decode [(0x91 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x92, b1..b18] = some (.bytes [b1..b18], [])` — the
    canonical eighteen-byte short-string encoding. -/
theorem decode_eighteen_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 : Byte) :
    decode [(0x92 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x93, b1..b19] = some (.bytes [b1..b19], [])` — the
    canonical nineteen-byte short-string encoding. -/
theorem decode_nineteen_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 : Byte) :
    decode [(0x93 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x94, b1..b20] = some (.bytes [b1..b20], [])` — the
    canonical twenty-byte short-string encoding. -/
theorem decode_twenty_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 : Byte) :
    decode [(0x94 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x95, b1..b21] = some (.bytes [b1..b21], [])` — the
    canonical twenty-one-byte short-string encoding. -/
theorem decode_twenty_one_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 : Byte) :
    decode [(0x95 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x96, b1..b22] = some (.bytes [b1..b22], [])` — the
    canonical twenty-two-byte short-string encoding. -/
theorem decode_twenty_two_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 :
      Byte) :
    decode [(0x96 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x97, b1..b23] = some (.bytes [b1..b23], [])` — the
    canonical twenty-three-byte short-string encoding. -/
theorem decode_twenty_three_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 : Byte) :
    decode [(0x97 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x98, b1..b24] = some (.bytes [b1..b24], [])` — the
    canonical twenty-four-byte short-string encoding. -/
theorem decode_twenty_four_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 : Byte) :
    decode [(0x98 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x99, b1..b25] = some (.bytes [b1..b25], [])` — the
    canonical twenty-five-byte short-string encoding. -/
theorem decode_twenty_five_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 : Byte) :
    decode [(0x99 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x9A, b1..b26] = some (.bytes [b1..b26], [])` — the
    canonical twenty-six-byte short-string encoding. -/
theorem decode_twenty_six_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 : Byte) :
    decode [(0x9A : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x9B, b1..b27] = some (.bytes [b1..b27], [])` — the
    canonical twenty-seven-byte short-string encoding. -/
theorem decode_twenty_seven_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 : Byte) :
    decode [(0x9B : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x9C, b1..b28] = some (.bytes [b1..b28], [])` — the
    canonical twenty-eight-byte short-string encoding. -/
theorem decode_twenty_eight_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 : Byte) :
    decode [(0x9C : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x9D, b1..b29] = some (.bytes [b1..b29], [])` — the
    canonical twenty-nine-byte short-string encoding. -/
theorem decode_twenty_nine_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 : Byte) :
    decode [(0x9D : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x9E, b1..b30] = some (.bytes [b1..b30], [])` — the
    canonical thirty-byte short-string encoding. -/
theorem decode_thirty_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 : Byte) :
    decode [(0x9E : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0x9F, b1..b31] = some (.bytes [b1..b31], [])` — the
    canonical thirty-one-byte short-string encoding. -/
theorem decode_thirty_one_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 : Byte) :
    decode [(0x9F : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xA0, b1..b32] = some (.bytes [b1..b32], [])` — the
    canonical thirty-two-byte short-string encoding. -/
theorem decode_thirty_two_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 : Byte) :
    decode [(0xA0 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xA1, b1..b33] = some (.bytes [b1..b33], [])` — the
    canonical thirty-three-byte short-string encoding. -/
theorem decode_thirty_three_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 : Byte) :
    decode [(0xA1 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xA2, b1..b34] = some (.bytes [b1..b34], [])` — the
    canonical thirty-four-byte short-string encoding. -/
theorem decode_thirty_four_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 : Byte) :
    decode [(0xA2 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xA3, b1..b35] = some (.bytes [b1..b35], [])` — the
    canonical thirty-five-byte short-string encoding. -/
theorem decode_thirty_five_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 : Byte) :
    decode [(0xA3 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xA4, b1..b36] = some (.bytes [b1..b36], [])` — the
    canonical thirty-six-byte short-string encoding. -/
theorem decode_thirty_six_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 : Byte) :
    decode [(0xA4 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xA5, b1..b37] = some (.bytes [b1..b37], [])` — the
    canonical thirty-seven-byte short-string encoding. -/
theorem decode_thirty_seven_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 : Byte) :
    decode [(0xA5 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xA6, b1..b38] = some (.bytes [b1..b38], [])` — the
    canonical thirty-eight-byte short-string encoding. -/
theorem decode_thirty_eight_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 : Byte) :
    decode [(0xA6 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xA7, b1..b39] = some (.bytes [b1..b39], [])` — the
    canonical thirty-nine-byte short-string encoding. -/
theorem decode_thirty_nine_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 : Byte) :
    decode [(0xA7 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38, b39] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xA8, b1..b40] = some (.bytes [b1..b40], [])` — the
    canonical forty-byte short-string encoding. -/
theorem decode_forty_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 :
      Byte) :
    decode [(0xA8 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38, b39, b40] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xA9, b1..b41] = some (.bytes [b1..b41], [])` — the
    canonical forty-one-byte short-string encoding. -/
theorem decode_forty_one_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 :
      Byte) :
    decode [(0xA9 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xAA, b1..b42] = some (.bytes [b1..b42], [])` — the
    canonical forty-two-byte short-string encoding. -/
theorem decode_forty_two_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 :
      Byte) :
    decode [(0xAA : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xAB, b1..b43] = some (.bytes [b1..b43], [])` — the
    canonical forty-three-byte short-string encoding. -/
theorem decode_forty_three_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 : Byte) :
    decode [(0xAB : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xAC, b1..b44] = some (.bytes [b1..b44], [])` — the
    canonical forty-four-byte short-string encoding. -/
theorem decode_forty_four_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 : Byte) :
    decode [(0xAC : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xAD, b1..b45] = some (.bytes [b1..b45], [])` — the
    canonical forty-five-byte short-string encoding. -/
theorem decode_forty_five_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 : Byte) :
    decode [(0xAD : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xAE, b1..b46] = some (.bytes [b1..b46], [])` — the
    canonical forty-six-byte short-string encoding. -/
theorem decode_forty_six_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 : Byte) :
    decode [(0xAE : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xAF, b1..b47] = some (.bytes [b1..b47], [])` — the
    canonical forty-seven-byte short-string encoding. -/
theorem decode_forty_seven_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 : Byte) :
    decode [(0xAF : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46,
      b47] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xB0, b1..b48] = some (.bytes [b1..b48], [])` — the
    canonical forty-eight-byte short-string encoding. -/
theorem decode_forty_eight_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 : Byte) :
    decode [(0xB0 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46,
      b47, b48] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48],
        []) := by
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

/-- Five-byte short string:
    `encodeBytes [a, b, c, d, e] = [0x85, a, b, c, d, e]`. -/
theorem encodeBytes_quint (a b c d e : Byte) :
    encodeBytes [a, b, c, d, e] = [BitVec.ofNat 8 0x85, a, b, c, d, e] := by
  simp [encodeBytes]

/-- Six-byte short string:
    `encodeBytes [a, b, c, d, e, f] = [0x86, a, b, c, d, e, f]`. -/
theorem encodeBytes_sext (a b c d e f : Byte) :
    encodeBytes [a, b, c, d, e, f] =
      [BitVec.ofNat 8 0x86, a, b, c, d, e, f] := by
  simp [encodeBytes]

/-- Seven-byte short string:
    `encodeBytes [a, b, c, d, e, f, g] = [0x87, a, b, c, d, e, f, g]`. -/
theorem encodeBytes_sept (a b c d e f g : Byte) :
    encodeBytes [a, b, c, d, e, f, g] =
      [BitVec.ofNat 8 0x87, a, b, c, d, e, f, g] := by
  simp [encodeBytes]

/-- Eight-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h] = [0x88, a, b, c, d, e, f, g, h]`. -/
theorem encodeBytes_oct (a b c d e f g h : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h] =
      [BitVec.ofNat 8 0x88, a, b, c, d, e, f, g, h] := by
  simp [encodeBytes]

/-- Nine-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i] = [0x89, a, b, c, d, e, f, g, h, i]`. -/
theorem encodeBytes_nonuple (a b c d e f g h i : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i] =
      [BitVec.ofNat 8 0x89, a, b, c, d, e, f, g, h, i] := by
  simp [encodeBytes]

/-- Ten-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j] = [0x8A, a, b, c, d, e, f, g, h, i, j]`. -/
theorem encodeBytes_decuple (a b c d e f g h i j : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j] =
      [BitVec.ofNat 8 0x8A, a, b, c, d, e, f, g, h, i, j] := by
  simp [encodeBytes]

/-- Eleven-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k] =
    [0x8B, a, b, c, d, e, f, g, h, i, j, k]`. -/
theorem encodeBytes_undecuple (a b c d e f g h i j k : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k] =
      [BitVec.ofNat 8 0x8B, a, b, c, d, e, f, g, h, i, j, k] := by
  simp [encodeBytes]

/-- Twelve-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l] =
    [0x8C, a, b, c, d, e, f, g, h, i, j, k, l]`. -/
theorem encodeBytes_duodecuple (a b c d e f g h i j k l : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l] =
      [BitVec.ofNat 8 0x8C, a, b, c, d, e, f, g, h, i, j, k, l] := by
  simp [encodeBytes]

/-- Thirteen-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m] =
    [0x8D, a, b, c, d, e, f, g, h, i, j, k, l, m]`. -/
theorem encodeBytes_tredecuple (a b c d e f g h i j k l m : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m] =
      [BitVec.ofNat 8 0x8D, a, b, c, d, e, f, g, h, i, j, k, l, m] := by
  simp [encodeBytes]

/-- Fourteen-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n] =
    [0x8E, a, b, c, d, e, f, g, h, i, j, k, l, m, n]`. -/
theorem encodeBytes_quattuordecuple (a b c d e f g h i j k l m n : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n] =
      [BitVec.ofNat 8 0x8E, a, b, c, d, e, f, g, h, i, j, k, l, m, n] := by
  simp [encodeBytes]

/-- Fifteen-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o] =
    [0x8F, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o]`. -/
theorem encodeBytes_quindecuple (a b c d e f g h i j k l m n o : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o] =
      [BitVec.ofNat 8 0x8F, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o] := by
  simp [encodeBytes]

/-- Sixteen-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] =
    [0x90, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p]`. -/
theorem encodeBytes_sedecuple (a b c d e f g h i j k l m n o p : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] =
      [BitVec.ofNat 8 0x90, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] := by
  simp [encodeBytes]

/-- Seventeen-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q] =
    [0x91, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q]`. -/
theorem encodeBytes_septendecuple (a b c d e f g h i j k l m n o p q : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q] =
      [BitVec.ofNat 8 0x91, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q] := by
  simp [encodeBytes]

/-- Eighteen-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r] =
    [0x92, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r]`. -/
theorem encodeBytes_octodecuple (a b c d e f g h i j k l m n o p q r : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r] =
      [BitVec.ofNat 8 0x92, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r] := by
  simp [encodeBytes]

/-- Nineteen-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s] =
    [0x93, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s]`. -/
theorem encodeBytes_novemdecuple (a b c d e f g h i j k l m n o p q r s : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s] =
      [BitVec.ofNat 8 0x93, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s] := by
  simp [encodeBytes]

/-- Twenty-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t] =
    [0x94, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t]`. -/
theorem encodeBytes_viguple (a b c d e f g h i j k l m n o p q r s t : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t] =
      [BitVec.ofNat 8 0x94, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t] := by
  simp [encodeBytes]

/-- Twenty-one-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u] =
    [0x95, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u]`. -/
theorem encodeBytes_unviguple (a b c d e f g h i j k l m n o p q r s t u : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u] =
      [BitVec.ofNat 8 0x95, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u] := by
  simp [encodeBytes]

/-- Twenty-two-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v] =
    [0x96, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v]`. -/
theorem encodeBytes_duoviguple (a b c d e f g h i j k l m n o p q r s t u v : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v] =
      [BitVec.ofNat 8 0x96, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v] := by
  simp [encodeBytes]

/-- Twenty-three-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w] =
    [0x97, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w]`. -/
theorem encodeBytes_tresviguple (a b c d e f g h i j k l m n o p q r s t u v w : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w] =
      [BitVec.ofNat 8 0x97, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w] := by
  simp [encodeBytes]

/-- Twenty-four-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x] =
    [0x98, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x]`. -/
theorem encodeBytes_quattuorviguple
    (a b c d e f g h i j k l m n o p q r s t u v w x : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x] =
      [BitVec.ofNat 8 0x98, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x] := by
  simp [encodeBytes]

/-- Twenty-five-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y] =
    [0x99, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y]`. -/
theorem encodeBytes_quinviguple
    (a b c d e f g h i j k l m n o p q r s t u v w x y : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y] =
      [BitVec.ofNat 8 0x99, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y] := by
  simp [encodeBytes]

/-- Twenty-six-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z] =
    [0x9A, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z]`. -/
theorem encodeBytes_sesviguple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z] =
      [BitVec.ofNat 8 0x9A, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z] := by
  simp [encodeBytes]

/-- Twenty-seven-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa] =
    [0x9B, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa]`. -/
theorem encodeBytes_septemviguple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa] =
      [BitVec.ofNat 8 0x9B, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa] := by
  simp [encodeBytes]

/-- Twenty-eight-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab] =
    [0x9C, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab]`. -/
theorem encodeBytes_duodetrigintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab] =
      [BitVec.ofNat 8 0x9C, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab] := by
  simp [encodeBytes]

/-- Twenty-nine-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac] =
    [0x9D, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac]`. -/
theorem encodeBytes_undetrigintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac] =
      [BitVec.ofNat 8 0x9D, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac] := by
  simp [encodeBytes]

/-- Thirty-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad] =
    [0x9E, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad]`. -/
theorem encodeBytes_trigintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad] =
      [BitVec.ofNat 8 0x9E, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad] := by
  simp [encodeBytes]

/-- Thirty-one-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae] =
    [0x9F, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae]`. -/
theorem encodeBytes_untrigintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae] =
      [BitVec.ofNat 8 0x9F, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae] := by
  simp [encodeBytes]

/-- Thirty-two-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af] =
    [0xA0, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af]`. -/
theorem encodeBytes_duotrigintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af] =
      [BitVec.ofNat 8 0xA0, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af] := by
  simp [encodeBytes]

/-- Thirty-three-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag] =
    [0xA1, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag]`. -/
theorem encodeBytes_trestrigintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag] =
      [BitVec.ofNat 8 0xA1, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag] := by
  simp [encodeBytes]

/-- Thirty-four-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah] =
    [0xA2, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah]`. -/
theorem encodeBytes_quattuortrigintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah : Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah] =
      [BitVec.ofNat 8 0xA2, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah] := by
  simp [encodeBytes]

/-- Thirty-five-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai] =
    [0xA3, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai]`. -/
theorem encodeBytes_quintrigintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai] =
      [BitVec.ofNat 8 0xA3, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai] := by
  simp [encodeBytes]

/-- Thirty-six-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj] =
    [0xA4, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj]`. -/
theorem encodeBytes_sestrigintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj] =
      [BitVec.ofNat 8 0xA4, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj] := by
  simp [encodeBytes]

/-- Thirty-seven-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak] =
    [0xA5, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak]`. -/
theorem encodeBytes_septemtrigintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak] =
      [BitVec.ofNat 8 0xA5, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak] := by
  simp [encodeBytes]

/-- Thirty-eight-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al] =
    [0xA6, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al]`. -/
theorem encodeBytes_duodequadragintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al] =
      [BitVec.ofNat 8 0xA6, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al] := by
  simp [encodeBytes]

/-- Thirty-nine-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am] =
    [0xA7, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am]`. -/
theorem encodeBytes_undequadragintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am] =
      [BitVec.ofNat 8 0xA7, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am] := by
  simp [encodeBytes]

/-- Forty-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an] =
    [0xA8, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an]`. -/
theorem encodeBytes_quadragintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an] =
      [BitVec.ofNat 8 0xA8, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an] := by
  simp [encodeBytes]

/-- Forty-one-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao] =
    [0xA9, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao]`. -/
theorem encodeBytes_unquadragintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao] =
      [BitVec.ofNat 8 0xA9, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao] := by
  simp [encodeBytes]

/-- Forty-two-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap] =
    [0xAA, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap]`. -/
theorem encodeBytes_duoquadragintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap] =
      [BitVec.ofNat 8 0xAA, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao,
        ap] := by
  simp [encodeBytes]

/-- Forty-three-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq] =
    [0xAB, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq]`. -/
theorem encodeBytes_tresquadragintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq] =
      [BitVec.ofNat 8 0xAB, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao,
        ap, aq] := by
  simp [encodeBytes]

/-- Forty-four-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar] =
    [0xAC, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar]`. -/
theorem encodeBytes_quattuorquadragintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar] =
      [BitVec.ofNat 8 0xAC, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao,
        ap, aq, ar] := by
  simp [encodeBytes]

/-- Forty-five-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as] =
    [0xAD, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as]`. -/
theorem encodeBytes_quinquadragintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as] =
      [BitVec.ofNat 8 0xAD, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao,
        ap, aq, ar, as] := by
  simp [encodeBytes]

/-- Forty-six-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as, au] =
    [0xAE, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as, au]`. -/
theorem encodeBytes_sesquadragintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au] =
      [BitVec.ofNat 8 0xAE, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao,
        ap, aq, ar, as, au] := by
  simp [encodeBytes]

/-- Forty-seven-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as, au, av] =
    [0xAF, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as, au, av]`. -/
theorem encodeBytes_septemquadragintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av] =
      [BitVec.ofNat 8 0xAF, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao,
        ap, aq, ar, as, au, av] := by
  simp [encodeBytes]

/-- Forty-eight-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as, au, av, aw] =
    [0xB0, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as, au, av, aw]`. -/
theorem encodeBytes_octoquadragintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw] =
      [BitVec.ofNat 8 0xB0, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao,
        ap, aq, ar, as, au, av, aw] := by
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

/-- Single-byte round-trip for large bytes (`b ≥ 0x80`): encoded as the
    two-byte sequence `[0x81, b]`, then the decoder reads the prefix
    as a one-byte short string, applies the canonical-form check
    (which passes because `b ≥ 0x80`), and returns `.bytes [b]`. -/
theorem decode_encode_bytes_single_large (b : Byte) (h : ¬ b.toNat < 0x80) :
    decode (encode (.bytes [b])) = some (.bytes [b], []) := by
  rw [show encode (.bytes [b]) = [BitVec.ofNat 8 0x81, b] from
    encodeBytes_single_large b h]
  simp [decode, decodeAux, takeBytes, h]

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
