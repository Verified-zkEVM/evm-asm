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

/-- Forty-nine-byte short string (prefix `0xB1`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_forty_nine_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB1 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 :: b41 ::
          b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Fifty-byte short string (prefix `0xB2`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_fifty_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB2 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 :: b41 ::
          b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Fifty-one-byte short string (prefix `0xB3`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_fifty_one_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB3 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 :: b41 ::
          b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 :: b51 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Fifty-two-byte short string (prefix `0xB4`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_fifty_two_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB4 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 :: b41 ::
          b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 :: b51 ::
          b52 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Fifty-three-byte short string (prefix `0xB5`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_fifty_three_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB5 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 :: b41 ::
          b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 :: b51 ::
          b52 :: b53 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Fifty-four-byte short string (prefix `0xB6`). Multi-byte payload
    bypasses the canonical-form check. -/
theorem decodeAux_fifty_four_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB6 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 :: b41 ::
          b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 :: b51 ::
          b52 :: b53 :: b54 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Fifty-five-byte short string (prefix `0xB7`). This is the maximum
    short-string payload length before long-form byte strings. -/
theorem decodeAux_fifty_five_byte_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB7 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 ::
          b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 ::
          b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 ::
          b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 :: b41 ::
          b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 :: b51 ::
          b52 :: b53 :: b54 :: b55 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55],
        rest) := by
  simp [decodeAux, takeBytes]

/-- Fifty-six-byte long string (prefix `0xB8`, length byte `0x38`). This is
    the first byte-string payload length that must use long form. -/
theorem decodeAux_fifty_six_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x38 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Fifty-seven-byte long string (prefix `0xB8`, length byte `0x39`). -/
theorem decodeAux_fifty_seven_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x39 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Fifty-eight-byte long string (prefix `0xB8`, length byte `0x3A`). -/
theorem decodeAux_fifty_eight_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x3A : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Fifty-nine-byte long string (prefix `0xB8`, length byte `0x3B`). -/
theorem decodeAux_fifty_nine_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x3B : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Sixty-byte long string (prefix `0xB8`, length byte `0x3C`). -/
theorem decodeAux_sixty_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x3C : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Sixty-one-byte long string (prefix `0xB8`, length byte `0x3D`). -/
theorem decodeAux_sixty_one_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 :
      Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x3D : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Sixty-two-byte long string (prefix `0xB8`, length byte `0x3E`). -/
theorem decodeAux_sixty_two_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 :
      Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x3E : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: b62 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Sixty-three-byte long string (prefix `0xB8`, length byte `0x3F`). -/
theorem decodeAux_sixty_three_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x3F : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: b62 :: b63 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Sixty-four-byte long string (prefix `0xB8`, length byte `0x40`). -/
theorem decodeAux_sixty_four_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x40 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: b62 :: b63 :: b64 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Sixty-five-byte long string (prefix `0xB8`, length byte `0x41`). -/
theorem decodeAux_sixty_five_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x41 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: b62 :: b63 :: b64 :: b65 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Sixty-six-byte long string (prefix `0xB8`, length byte `0x42`). -/
theorem decodeAux_sixty_six_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x42 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: b62 :: b63 :: b64 :: b65 :: b66 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Sixty-seven-byte long string (prefix `0xB8`, length byte `0x43`). -/
theorem decodeAux_sixty_seven_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x43 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: b62 :: b63 :: b64 :: b65 :: b66 :: b67 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Sixty-eight-byte long string (prefix `0xB8`, length byte `0x44`). -/
theorem decodeAux_sixty_eight_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x44 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: b62 :: b63 :: b64 :: b65 :: b66 :: b67 :: b68 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Sixty-nine-byte long string (prefix `0xB8`, length byte `0x45`). -/
theorem decodeAux_sixty_nine_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x45 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: b62 :: b63 :: b64 :: b65 :: b66 :: b67 :: b68 :: b69 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Seventy-byte long string (prefix `0xB8`, length byte `0x46`). -/
theorem decodeAux_seventy_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x46 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: b62 :: b63 :: b64 :: b65 :: b66 :: b67 :: b68 :: b69 :: b70 ::
          rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Seventy-one-byte long string (prefix `0xB8`, length byte `0x47`). -/
theorem decodeAux_seventy_one_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x47 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: b62 :: b63 :: b64 :: b65 :: b66 :: b67 :: b68 :: b69 :: b70 ::
          b71 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Seventy-two-byte long string (prefix `0xB8`, length byte `0x48`). -/
theorem decodeAux_seventy_two_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x48 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: b62 :: b63 :: b64 :: b65 :: b66 :: b67 :: b68 :: b69 :: b70 ::
          b71 :: b72 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Seventy-three-byte long string (prefix `0xB8`, length byte `0x49`). -/
theorem decodeAux_seventy_three_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x49 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: b62 :: b63 :: b64 :: b65 :: b66 :: b67 :: b68 :: b69 :: b70 ::
          b71 :: b72 :: b73 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Seventy-four-byte long string (prefix `0xB8`, length byte `0x4A`). -/
theorem decodeAux_seventy_four_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x4A : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: b62 :: b63 :: b64 :: b65 :: b66 :: b67 :: b68 :: b69 :: b70 ::
          b71 :: b72 :: b73 :: b74 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Seventy-five-byte long string (prefix `0xB8`, length byte `0x4B`). -/
theorem decodeAux_seventy_five_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x4B : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: b62 :: b63 :: b64 :: b65 :: b66 :: b67 :: b68 :: b69 :: b70 ::
          b71 :: b72 :: b73 :: b74 :: b75 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Seventy-six-byte long string (prefix `0xB8`, length byte `0x4C`). -/
theorem decodeAux_seventy_six_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x4C : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: b62 :: b63 :: b64 :: b65 :: b66 :: b67 :: b68 :: b69 :: b70 ::
          b71 :: b72 :: b73 :: b74 :: b75 :: b76 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Seventy-seven-byte long string (prefix `0xB8`, length byte `0x4D`). -/
theorem decodeAux_seventy_seven_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 b77 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x4D : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: b62 :: b63 :: b64 :: b65 :: b66 :: b67 :: b68 :: b69 :: b70 ::
          b71 :: b72 :: b73 :: b74 :: b75 :: b76 :: b77 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76,
          b77],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Seventy-eight-byte long string (prefix `0xB8`, length byte `0x4E`). -/
theorem decodeAux_seventy_eight_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 b77 b78 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x4E : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: b62 :: b63 :: b64 :: b65 :: b66 :: b67 :: b68 :: b69 :: b70 ::
          b71 :: b72 :: b73 :: b74 :: b75 :: b76 :: b77 :: b78 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76,
          b77, b78],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Seventy-nine-byte long string (prefix `0xB8`, length byte `0x4F`). -/
theorem decodeAux_seventy_nine_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 b77 b78 b79 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x4F : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: b62 :: b63 :: b64 :: b65 :: b66 :: b67 :: b68 :: b69 :: b70 ::
          b71 :: b72 :: b73 :: b74 :: b75 :: b76 :: b77 :: b78 :: b79 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76,
          b77, b78, b79],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Eighty-byte long string (prefix `0xB8`, length byte `0x50`). -/
theorem decodeAux_eighty_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 b77 b78 b79 b80 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x50 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: b62 :: b63 :: b64 :: b65 :: b66 :: b67 :: b68 :: b69 :: b70 ::
          b71 :: b72 :: b73 :: b74 :: b75 :: b76 :: b77 :: b78 :: b79 :: b80 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76,
          b77, b78, b79, b80],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Eighty-one-byte long string (prefix `0xB8`, length byte `0x51`). -/
theorem decodeAux_eighty_one_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 b77 b78 b79 b80 b81 :
      Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x51 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: b62 :: b63 :: b64 :: b65 :: b66 :: b67 :: b68 :: b69 :: b70 ::
          b71 :: b72 :: b73 :: b74 :: b75 :: b76 :: b77 :: b78 :: b79 :: b80 ::
          b81 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76,
          b77, b78, b79, b80, b81],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Eighty-two-byte long string (prefix `0xB8`, length byte `0x52`). -/
theorem decodeAux_eighty_two_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 b77 b78 b79 b80 b81 b82 :
      Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x52 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: b62 :: b63 :: b64 :: b65 :: b66 :: b67 :: b68 :: b69 :: b70 ::
          b71 :: b72 :: b73 :: b74 :: b75 :: b76 :: b77 :: b78 :: b79 :: b80 ::
          b81 :: b82 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76,
          b77, b78, b79, b80, b81, b82],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Eighty-three-byte long string (prefix `0xB8`, length byte `0x53`). -/
theorem decodeAux_eighty_three_byte_long_string
    (fuel : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 b77 b78 b79 b80 b81 b82
      b83 : Byte)
    (rest : List Byte) :
    decodeAux (fuel + 1)
        ((0xB8 : Byte) :: (0x53 : Byte) :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
          b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 ::
          b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 ::
          b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 ::
          b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 ::
          b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 ::
          b61 :: b62 :: b63 :: b64 :: b65 :: b66 :: b67 :: b68 :: b69 :: b70 ::
          b71 :: b72 :: b73 :: b74 :: b75 :: b76 :: b77 :: b78 :: b79 :: b80 ::
          b81 :: b82 :: b83 :: rest) =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76,
          b77, b78, b79, b80, b81, b82, b83],
        rest) := by
  simp [decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- Concrete 84-byte long-string payload used by the executable examples below. -/
def rlpEightyFourBytePayload : List Byte :=
  List.replicate 84 (0x42 : Byte)

/-- Executable example: 84-byte long string (prefix `0xB8`, length byte `0x54`). -/
theorem decodeAux_eighty_four_byte_long_string :
    decodeAux 100 ([(0xB8 : Byte), (0x54 : Byte)] ++ rlpEightyFourBytePayload) =
      some (.bytes rlpEightyFourBytePayload, []) := by
  native_decide

/-- Concrete 85-byte long-string payload used by the executable examples below. -/
def rlpEightyFiveBytePayload : List Byte :=
  List.replicate 85 (0x43 : Byte)

/-- Executable example: 85-byte long string (prefix `0xB8`, length byte `0x55`). -/
theorem decodeAux_eighty_five_byte_long_string :
    decodeAux 100 ([(0xB8 : Byte), (0x55 : Byte)] ++ rlpEightyFiveBytePayload) =
      some (.bytes rlpEightyFiveBytePayload, []) := by
  native_decide

/-- Concrete 86-byte long-string payload used by the executable examples below. -/
def rlpEightySixBytePayload : List Byte :=
  List.replicate 86 (0x44 : Byte)

/-- Executable example: 86-byte long string (prefix `0xB8`, length byte `0x56`). -/
theorem decodeAux_eighty_six_byte_long_string :
    decodeAux 100 ([(0xB8 : Byte), (0x56 : Byte)] ++ rlpEightySixBytePayload) =
      some (.bytes rlpEightySixBytePayload, []) := by
  native_decide

/-- Concrete 87-byte long-string payload used by the executable examples below. -/
def rlpEightySevenBytePayload : List Byte :=
  List.replicate 87 (0x45 : Byte)

/-- Executable example: 87-byte long string (prefix `0xB8`, length byte `0x57`). -/
theorem decodeAux_eighty_seven_byte_long_string :
    decodeAux 100 ([(0xB8 : Byte), (0x57 : Byte)] ++ rlpEightySevenBytePayload) =
      some (.bytes rlpEightySevenBytePayload, []) := by
  native_decide

/-- Concrete 88-byte long-string payload used by the executable examples below. -/
def rlpEightyEightBytePayload : List Byte :=
  List.replicate 88 (0x46 : Byte)

/-- Executable example: 88-byte long string (prefix `0xB8`, length byte `0x58`). -/
theorem decodeAux_eighty_eight_byte_long_string :
    decodeAux 100 ([(0xB8 : Byte), (0x58 : Byte)] ++ rlpEightyEightBytePayload) =
      some (.bytes rlpEightyEightBytePayload, []) := by
  native_decide

/-- Concrete 89-byte long-string payload used by the executable examples below. -/
def rlpEightyNineBytePayload : List Byte :=
  List.replicate 89 (0x47 : Byte)

/-- Executable example: 89-byte long string (prefix `0xB8`, length byte `0x59`). -/
theorem decodeAux_eighty_nine_byte_long_string :
    decodeAux 100 ([(0xB8 : Byte), (0x59 : Byte)] ++ rlpEightyNineBytePayload) =
      some (.bytes rlpEightyNineBytePayload, []) := by
  native_decide

/-- Concrete 90-byte long-string payload used by the executable examples below. -/
def rlpNinetyBytePayload : List Byte :=
  List.replicate 90 (0x48 : Byte)

/-- Executable example: 90-byte long string (prefix `0xB8`, length byte `0x5A`). -/
theorem decodeAux_ninety_byte_long_string :
    decodeAux 100 ([(0xB8 : Byte), (0x5A : Byte)] ++ rlpNinetyBytePayload) =
      some (.bytes rlpNinetyBytePayload, []) := by
  native_decide

/-- Concrete 91-byte long-string payload used by the executable examples below. -/
def rlpNinetyOneBytePayload : List Byte :=
  List.replicate 91 (0x49 : Byte)

/-- Executable example: 91-byte long string (prefix `0xB8`, length byte `0x5B`). -/
theorem decodeAux_ninety_one_byte_long_string :
    decodeAux 100 ([(0xB8 : Byte), (0x5B : Byte)] ++ rlpNinetyOneBytePayload) =
      some (.bytes rlpNinetyOneBytePayload, []) := by
  native_decide

/-- Concrete 92-byte long-string payload used by the executable examples below. -/
def rlpNinetyTwoBytePayload : List Byte :=
  List.replicate 92 (0x4A : Byte)

/-- Executable example: 92-byte long string (prefix `0xB8`, length byte `0x5C`). -/
theorem decodeAux_ninety_two_byte_long_string :
    decodeAux 100 ([(0xB8 : Byte), (0x5C : Byte)] ++ rlpNinetyTwoBytePayload) =
      some (.bytes rlpNinetyTwoBytePayload, []) := by
  native_decide

/-- Concrete 93-byte long-string payload used by the executable examples below. -/
def rlpNinetyThreeBytePayload : List Byte :=
  List.replicate 93 (0x4B : Byte)

/-- Executable example: 93-byte long string (prefix `0xB8`, length byte `0x5D`). -/
theorem decodeAux_ninety_three_byte_long_string :
    decodeAux 100 ([(0xB8 : Byte), (0x5D : Byte)] ++ rlpNinetyThreeBytePayload) =
      some (.bytes rlpNinetyThreeBytePayload, []) := by
  native_decide

/-- Concrete 94-byte long-string payload used by the executable examples below. -/
def rlpNinetyFourBytePayload : List Byte :=
  List.replicate 94 (0x4C : Byte)

/-- Executable example: 94-byte long string (prefix `0xB8`, length byte `0x5E`). -/
theorem decodeAux_ninety_four_byte_long_string :
    decodeAux 100 ([(0xB8 : Byte), (0x5E : Byte)] ++ rlpNinetyFourBytePayload) =
      some (.bytes rlpNinetyFourBytePayload, []) := by
  native_decide

/-- Concrete 95-byte long-string payload used by the executable examples below. -/
def rlpNinetyFiveBytePayload : List Byte :=
  List.replicate 95 (0x4D : Byte)

/-- Executable example: 95-byte long string (prefix `0xB8`, length byte `0x5F`). -/
theorem decodeAux_ninety_five_byte_long_string :
    decodeAux 100 ([(0xB8 : Byte), (0x5F : Byte)] ++ rlpNinetyFiveBytePayload) =
      some (.bytes rlpNinetyFiveBytePayload, []) := by
  native_decide

/-- Concrete 96-byte long-string payload used by the executable examples below. -/
def rlpNinetySixBytePayload : List Byte :=
  List.replicate 96 (0x4E : Byte)

/-- Executable example: 96-byte long string (prefix `0xB8`, length byte `0x60`). -/
theorem decodeAux_ninety_six_byte_long_string :
    decodeAux 100 ([(0xB8 : Byte), (0x60 : Byte)] ++ rlpNinetySixBytePayload) =
      some (.bytes rlpNinetySixBytePayload, []) := by
  native_decide

/-- Concrete 97-byte long-string payload used by the executable examples below. -/
def rlpNinetySevenBytePayload : List Byte :=
  List.replicate 97 (0x4F : Byte)

/-- Executable example: 97-byte long string (prefix `0xB8`, length byte `0x61`). -/
theorem decodeAux_ninety_seven_byte_long_string :
    decodeAux 100 ([(0xB8 : Byte), (0x61 : Byte)] ++ rlpNinetySevenBytePayload) =
      some (.bytes rlpNinetySevenBytePayload, []) := by
  native_decide

/-- Concrete 98-byte long-string payload used by the executable examples below. -/
def rlpNinetyEightBytePayload : List Byte :=
  List.replicate 98 (0x50 : Byte)

/-- Executable example: 98-byte long string (prefix `0xB8`, length byte `0x62`). -/
theorem decodeAux_ninety_eight_byte_long_string :
    decodeAux 100 ([(0xB8 : Byte), (0x62 : Byte)] ++ rlpNinetyEightBytePayload) =
      some (.bytes rlpNinetyEightBytePayload, []) := by
  native_decide

/-- Concrete 99-byte long-string payload used by the executable examples below. -/
def rlpNinetyNineBytePayload : List Byte :=
  List.replicate 99 (0x51 : Byte)

/-- Executable example: 99-byte long string (prefix `0xB8`, length byte `0x63`). -/
theorem decodeAux_ninety_nine_byte_long_string :
    decodeAux 100 ([(0xB8 : Byte), (0x63 : Byte)] ++ rlpNinetyNineBytePayload) =
      some (.bytes rlpNinetyNineBytePayload, []) := by
  native_decide

/-- Concrete 100-byte long-string payload used by the executable examples below. -/
def rlpOneHundredBytePayload : List Byte :=
  List.replicate 100 (0x52 : Byte)

/-- Executable example: 100-byte long string (prefix `0xB8`, length byte `0x64`). -/
theorem decodeAux_one_hundred_byte_long_string :
    decodeAux 100 ([(0xB8 : Byte), (0x64 : Byte)] ++ rlpOneHundredBytePayload) =
      some (.bytes rlpOneHundredBytePayload, []) := by
  native_decide

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

/-- `decode [0xB1, b1..b49] = some (.bytes [b1..b49], [])` — the
    canonical forty-nine-byte short-string encoding. -/
theorem decode_forty_nine_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 : Byte) :
    decode [(0xB1 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46,
      b47, b48, b49] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xB2, b1..b50] = some (.bytes [b1..b50], [])` — the
    canonical fifty-byte short-string encoding. -/
theorem decode_fifty_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 : Byte) :
    decode [(0xB2 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46,
      b47, b48, b49, b50] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xB3, b1..b51] = some (.bytes [b1..b51], [])` — the
    canonical fifty-one-byte short-string encoding. -/
theorem decode_fifty_one_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 : Byte) :
    decode [(0xB3 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46,
      b47, b48, b49, b50, b51] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xB4, b1..b52] = some (.bytes [b1..b52], [])` — the
    canonical fifty-two-byte short-string encoding. -/
theorem decode_fifty_two_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 : Byte) :
    decode [(0xB4 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46,
      b47, b48, b49, b50, b51, b52] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xB5, b1..b53] = some (.bytes [b1..b53], [])` — the
    canonical fifty-three-byte short-string encoding. -/
theorem decode_fifty_three_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 : Byte) :
    decode [(0xB5 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46,
      b47, b48, b49, b50, b51, b52, b53] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xB6, b1..b54] = some (.bytes [b1..b54], [])` — the
    canonical fifty-four-byte short-string encoding. -/
theorem decode_fifty_four_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 : Byte) :
    decode [(0xB6 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46,
      b47, b48, b49, b50, b51, b52, b53, b54] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xB7, b1..b55] = some (.bytes [b1..b55], [])` — the
    canonical maximum-length short-string encoding. -/
theorem decode_fifty_five_byte_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 : Byte) :
    decode [(0xB7 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
      b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46,
      b47, b48, b49, b50, b51, b52, b53, b54, b55] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55],
        []) := by
  simp [decode, decodeAux, takeBytes]

/-- `decode [0xB8, 0x38, b1..b56] = some (.bytes [b1..b56], [])` — the
    canonical first long-form byte-string encoding. -/
theorem decode_fifty_six_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 : Byte) :
    decode [(0xB8 : Byte), (0x38 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x39, b1..b57] = some (.bytes [b1..b57], [])`. -/
theorem decode_fifty_seven_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 : Byte) :
    decode [(0xB8 : Byte), (0x39 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x3A, b1..b58] = some (.bytes [b1..b58], [])`. -/
theorem decode_fifty_eight_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 : Byte) :
    decode [(0xB8 : Byte), (0x3A : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x3B, b1..b59] = some (.bytes [b1..b59], [])`. -/
theorem decode_fifty_nine_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 : Byte) :
    decode [(0xB8 : Byte), (0x3B : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x3C, b1..b60] = some (.bytes [b1..b60], [])`. -/
theorem decode_sixty_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 : Byte) :
    decode [(0xB8 : Byte), (0x3C : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x3D, b1..b61] = some (.bytes [b1..b61], [])`. -/
theorem decode_sixty_one_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 :
      Byte) :
    decode [(0xB8 : Byte), (0x3D : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x3E, b1..b62] = some (.bytes [b1..b62], [])`. -/
theorem decode_sixty_two_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 :
      Byte) :
    decode [(0xB8 : Byte), (0x3E : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61, b62] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x3F, b1..b63] = some (.bytes [b1..b63], [])`. -/
theorem decode_sixty_three_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 : Byte) :
    decode [(0xB8 : Byte), (0x3F : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61, b62, b63] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x40, b1..b64] = some (.bytes [b1..b64], [])`. -/
theorem decode_sixty_four_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 : Byte) :
    decode [(0xB8 : Byte), (0x40 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61, b62, b63, b64] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x41, b1..b65] = some (.bytes [b1..b65], [])`. -/
theorem decode_sixty_five_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 : Byte) :
    decode [(0xB8 : Byte), (0x41 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61, b62, b63, b64, b65] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x42, b1..b66] = some (.bytes [b1..b66], [])`. -/
theorem decode_sixty_six_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 : Byte) :
    decode [(0xB8 : Byte), (0x42 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x43, b1..b67] = some (.bytes [b1..b67], [])`. -/
theorem decode_sixty_seven_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 : Byte) :
    decode [(0xB8 : Byte), (0x43 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x44, b1..b68] = some (.bytes [b1..b68], [])`. -/
theorem decode_sixty_eight_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 : Byte) :
    decode [(0xB8 : Byte), (0x44 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x45, b1..b69] = some (.bytes [b1..b69], [])`. -/
theorem decode_sixty_nine_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 : Byte) :
    decode [(0xB8 : Byte), (0x45 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x46, b1..b70] = some (.bytes [b1..b70], [])`. -/
theorem decode_seventy_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 : Byte) :
    decode [(0xB8 : Byte), (0x46 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x47, b1..b71] = some (.bytes [b1..b71], [])`. -/
theorem decode_seventy_one_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 : Byte) :
    decode [(0xB8 : Byte), (0x47 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70,
      b71] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x48, b1..b72] = some (.bytes [b1..b72], [])`. -/
theorem decode_seventy_two_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 : Byte) :
    decode [(0xB8 : Byte), (0x48 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70,
      b71, b72] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x49, b1..b73] = some (.bytes [b1..b73], [])`. -/
theorem decode_seventy_three_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 : Byte) :
    decode [(0xB8 : Byte), (0x49 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70,
      b71, b72, b73] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x4A, b1..b74] = some (.bytes [b1..b74], [])`. -/
theorem decode_seventy_four_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 : Byte) :
    decode [(0xB8 : Byte), (0x4A : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70,
      b71, b72, b73, b74] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x4B, b1..b75] = some (.bytes [b1..b75], [])`. -/
theorem decode_seventy_five_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 : Byte) :
    decode [(0xB8 : Byte), (0x4B : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70,
      b71, b72, b73, b74, b75] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x4C, b1..b76] = some (.bytes [b1..b76], [])`. -/
theorem decode_seventy_six_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 : Byte) :
    decode [(0xB8 : Byte), (0x4C : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70,
      b71, b72, b73, b74, b75, b76] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x4D, b1..b77] = some (.bytes [b1..b77], [])`. -/
theorem decode_seventy_seven_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 b77 : Byte) :
    decode [(0xB8 : Byte), (0x4D : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70,
      b71, b72, b73, b74, b75, b76, b77] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76,
          b77],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x4E, b1..b78] = some (.bytes [b1..b78], [])`. -/
theorem decode_seventy_eight_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 b77 b78 : Byte) :
    decode [(0xB8 : Byte), (0x4E : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70,
      b71, b72, b73, b74, b75, b76, b77, b78] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76,
          b77, b78],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x4F, b1..b79] = some (.bytes [b1..b79], [])`. -/
theorem decode_seventy_nine_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 b77 b78 b79 : Byte) :
    decode [(0xB8 : Byte), (0x4F : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70,
      b71, b72, b73, b74, b75, b76, b77, b78, b79] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76,
          b77, b78, b79],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x50, b1..b80] = some (.bytes [b1..b80], [])`. -/
theorem decode_eighty_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 b77 b78 b79 b80 : Byte) :
    decode [(0xB8 : Byte), (0x50 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70,
      b71, b72, b73, b74, b75, b76, b77, b78, b79, b80] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76,
          b77, b78, b79, b80],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x51, b1..b81] = some (.bytes [b1..b81], [])`. -/
theorem decode_eighty_one_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 b77 b78 b79 b80 b81 :
      Byte) :
    decode [(0xB8 : Byte), (0x51 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70,
      b71, b72, b73, b74, b75, b76, b77, b78, b79, b80, b81] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76,
          b77, b78, b79, b80, b81],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x52, b1..b82] = some (.bytes [b1..b82], [])`. -/
theorem decode_eighty_two_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 b77 b78 b79 b80 b81 b82 :
      Byte) :
    decode [(0xB8 : Byte), (0x52 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70,
      b71, b72, b73, b74, b75, b76, b77, b78, b79, b80, b81, b82] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76,
          b77, b78, b79, b80, b81, b82],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x53, b1..b83] = some (.bytes [b1..b83], [])`. -/
theorem decode_eighty_three_byte_long_string
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42
      b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62
      b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 b77 b78 b79 b80 b81 b82
      b83 : Byte) :
    decode [(0xB8 : Byte), (0x53 : Byte), b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
      b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25,
      b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40,
      b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55,
      b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70,
      b71, b72, b73, b74, b75, b76, b77, b78, b79, b80, b81, b82, b83] =
      some (.bytes
        [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
          b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32,
          b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47,
          b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61,
          b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76,
          b77, b78, b79, b80, b81, b82, b83],
        []) := by
  simp [decode, decodeAux, readLength, takeBytes, Nat.fromBytesBE]

/-- `decode [0xB8, 0x54] ++ rlpEightyFourBytePayload`
    returns the concrete 84-byte payload. -/
theorem decode_eighty_four_byte_long_string :
    decode ([(0xB8 : Byte), (0x54 : Byte)] ++ rlpEightyFourBytePayload) =
      some (.bytes rlpEightyFourBytePayload, []) := by
  native_decide

/-- `decode [0xB8, 0x55] ++ rlpEightyFiveBytePayload`
    returns the concrete 85-byte payload. -/
theorem decode_eighty_five_byte_long_string :
    decode ([(0xB8 : Byte), (0x55 : Byte)] ++ rlpEightyFiveBytePayload) =
      some (.bytes rlpEightyFiveBytePayload, []) := by
  native_decide

/-- `decode [0xB8, 0x56] ++ rlpEightySixBytePayload`
    returns the concrete 86-byte payload. -/
theorem decode_eighty_six_byte_long_string :
    decode ([(0xB8 : Byte), (0x56 : Byte)] ++ rlpEightySixBytePayload) =
      some (.bytes rlpEightySixBytePayload, []) := by
  native_decide

/-- `decode [0xB8, 0x57] ++ rlpEightySevenBytePayload`
    returns the concrete 87-byte payload. -/
theorem decode_eighty_seven_byte_long_string :
    decode ([(0xB8 : Byte), (0x57 : Byte)] ++ rlpEightySevenBytePayload) =
      some (.bytes rlpEightySevenBytePayload, []) := by
  native_decide

/-- `decode [0xB8, 0x58] ++ rlpEightyEightBytePayload`
    returns the concrete 88-byte payload. -/
theorem decode_eighty_eight_byte_long_string :
    decode ([(0xB8 : Byte), (0x58 : Byte)] ++ rlpEightyEightBytePayload) =
      some (.bytes rlpEightyEightBytePayload, []) := by
  native_decide

/-- `decode [0xB8, 0x59] ++ rlpEightyNineBytePayload`
    returns the concrete 89-byte payload. -/
theorem decode_eighty_nine_byte_long_string :
    decode ([(0xB8 : Byte), (0x59 : Byte)] ++ rlpEightyNineBytePayload) =
      some (.bytes rlpEightyNineBytePayload, []) := by
  native_decide

/-- `decode [0xB8, 0x5A] ++ rlpNinetyBytePayload`
    returns the concrete 90-byte payload. -/
theorem decode_ninety_byte_long_string :
    decode ([(0xB8 : Byte), (0x5A : Byte)] ++ rlpNinetyBytePayload) =
      some (.bytes rlpNinetyBytePayload, []) := by
  native_decide

/-- `decode [0xB8, 0x5B] ++ rlpNinetyOneBytePayload`
    returns the concrete 91-byte payload. -/
theorem decode_ninety_one_byte_long_string :
    decode ([(0xB8 : Byte), (0x5B : Byte)] ++ rlpNinetyOneBytePayload) =
      some (.bytes rlpNinetyOneBytePayload, []) := by
  native_decide

/-- `decode [0xB8, 0x5C] ++ rlpNinetyTwoBytePayload`
    returns the concrete 92-byte payload. -/
theorem decode_ninety_two_byte_long_string :
    decode ([(0xB8 : Byte), (0x5C : Byte)] ++ rlpNinetyTwoBytePayload) =
      some (.bytes rlpNinetyTwoBytePayload, []) := by
  native_decide

/-- `decode [0xB8, 0x5D] ++ rlpNinetyThreeBytePayload`
    returns the concrete 93-byte payload. -/
theorem decode_ninety_three_byte_long_string :
    decode ([(0xB8 : Byte), (0x5D : Byte)] ++ rlpNinetyThreeBytePayload) =
      some (.bytes rlpNinetyThreeBytePayload, []) := by
  native_decide

/-- `decode [0xB8, 0x5E] ++ rlpNinetyFourBytePayload`
    returns the concrete 94-byte payload. -/
theorem decode_ninety_four_byte_long_string :
    decode ([(0xB8 : Byte), (0x5E : Byte)] ++ rlpNinetyFourBytePayload) =
      some (.bytes rlpNinetyFourBytePayload, []) := by
  native_decide

/-- `decode [0xB8, 0x5F] ++ rlpNinetyFiveBytePayload`
    returns the concrete 95-byte payload. -/
theorem decode_ninety_five_byte_long_string :
    decode ([(0xB8 : Byte), (0x5F : Byte)] ++ rlpNinetyFiveBytePayload) =
      some (.bytes rlpNinetyFiveBytePayload, []) := by
  native_decide

/-- `decode [0xB8, 0x60] ++ rlpNinetySixBytePayload`
    returns the concrete 96-byte payload. -/
theorem decode_ninety_six_byte_long_string :
    decode ([(0xB8 : Byte), (0x60 : Byte)] ++ rlpNinetySixBytePayload) =
      some (.bytes rlpNinetySixBytePayload, []) := by
  native_decide

/-- `decode [0xB8, 0x61] ++ rlpNinetySevenBytePayload`
    returns the concrete 97-byte payload. -/
theorem decode_ninety_seven_byte_long_string :
    decode ([(0xB8 : Byte), (0x61 : Byte)] ++ rlpNinetySevenBytePayload) =
      some (.bytes rlpNinetySevenBytePayload, []) := by
  native_decide

/-- `decode [0xB8, 0x62] ++ rlpNinetyEightBytePayload`
    returns the concrete 98-byte payload. -/
theorem decode_ninety_eight_byte_long_string :
    decode ([(0xB8 : Byte), (0x62 : Byte)] ++ rlpNinetyEightBytePayload) =
      some (.bytes rlpNinetyEightBytePayload, []) := by
  native_decide

/-- `decode [0xB8, 0x63] ++ rlpNinetyNineBytePayload`
    returns the concrete 99-byte payload. -/
theorem decode_ninety_nine_byte_long_string :
    decode ([(0xB8 : Byte), (0x63 : Byte)] ++ rlpNinetyNineBytePayload) =
      some (.bytes rlpNinetyNineBytePayload, []) := by
  native_decide

/-- `decode [0xB8, 0x64] ++ rlpOneHundredBytePayload`
    returns the concrete 100-byte payload. -/
theorem decode_one_hundred_byte_long_string :
    decode ([(0xB8 : Byte), (0x64 : Byte)] ++ rlpOneHundredBytePayload) =
      some (.bytes rlpOneHundredBytePayload, []) := by
  native_decide

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

/-- Forty-nine-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax] =
    [0xB1, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax]`. -/
theorem encodeBytes_novemquadragintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax] =
      [BitVec.ofNat 8 0xB1, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao,
        ap, aq, ar, as, au, av, aw, ax] := by
  simp [encodeBytes]

/-- Fifty-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay] =
    [0xB2, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay]`. -/
theorem encodeBytes_quinquagintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay] =
      [BitVec.ofNat 8 0xB2, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao,
        ap, aq, ar, as, au, av, aw, ax, ay] := by
  simp [encodeBytes]

/-- Fifty-one-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az] =
    [0xB3, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az]`. -/
theorem encodeBytes_unquinquagintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az] =
      [BitVec.ofNat 8 0xB3, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao,
        ap, aq, ar, as, au, av, aw, ax, ay, az] := by
  simp [encodeBytes]

/-- Fifty-two-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba] =
    [0xB4, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba]`. -/
theorem encodeBytes_duoquinquagintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba] =
      [BitVec.ofNat 8 0xB4, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao,
        ap, aq, ar, as, au, av, aw, ax, ay, az, ba] := by
  simp [encodeBytes]

/-- Fifty-three-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb] =
    [0xB5, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb]`. -/
theorem encodeBytes_tresquinquagintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb] =
      [BitVec.ofNat 8 0xB5, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao,
        ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb] := by
  simp [encodeBytes]

/-- Fifty-four-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc] =
    [0xB6, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc]`. -/
theorem encodeBytes_quattuorquinquagintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc] =
      [BitVec.ofNat 8 0xB6, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao,
        ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc] := by
  simp [encodeBytes]

/-- Fifty-five-byte short string:
    `encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd] =
    [0xB7, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd]`. -/
theorem encodeBytes_quinquinquagintuple
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd] =
      [BitVec.ofNat 8 0xB7, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t,
        u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao,
        ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd] := by
  simp [encodeBytes]

/-- Fifty-six-byte long string:
    `encodeBytes [a, b, ..., be] = [0xB8, 0x38, a, b, ..., be]`. -/
theorem encodeBytes_fifty_six_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x38, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Fifty-seven-byte long string:
    `encodeBytes [a, b, ..., bf] = [0xB8, 0x39, a, b, ..., bf]`. -/
theorem encodeBytes_fifty_seven_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x39, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Fifty-eight-byte long string:
    `encodeBytes [a, b, ..., bg] = [0xB8, 0x3A, a, b, ..., bg]`. -/
theorem encodeBytes_fifty_eight_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x3A, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Fifty-nine-byte long string:
    `encodeBytes [a, b, ..., bh] = [0xB8, 0x3B, a, b, ..., bh]`. -/
theorem encodeBytes_fifty_nine_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x3B, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Sixty-byte long string:
    `encodeBytes [a, b, ..., bi] = [0xB8, 0x3C, a, b, ..., bi]`. -/
theorem encodeBytes_sixty_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x3C, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Sixty-one-byte long string:
    `encodeBytes [a, b, ..., bj] = [0xB8, 0x3D, a, b, ..., bj]`. -/
theorem encodeBytes_sixty_one_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x3D, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Sixty-two-byte long string:
    `encodeBytes [a, b, ..., bk] = [0xB8, 0x3E, a, b, ..., bk]`. -/
theorem encodeBytes_sixty_two_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj, bk] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x3E, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj, bk] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Sixty-three-byte long string:
    `encodeBytes [a, b, ..., bl] = [0xB8, 0x3F, a, b, ..., bl]`. -/
theorem encodeBytes_sixty_three_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk bl :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj, bk, bl] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x3F, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj, bk, bl] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Sixty-four-byte long string:
    `encodeBytes [a, b, ..., bm] = [0xB8, 0x40, a, b, ..., bm]`. -/
theorem encodeBytes_sixty_four_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk bl bm :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj, bk, bl, bm] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x40, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj, bk, bl, bm] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Sixty-five-byte long string:
    `encodeBytes [a, b, ..., bn] = [0xB8, 0x41, a, b, ..., bn]`. -/
theorem encodeBytes_sixty_five_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk bl bm bn :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj, bk, bl, bm, bn] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x41, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj, bk, bl, bm, bn] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Sixty-six-byte long string:
    `encodeBytes [a, b, ..., bo] = [0xB8, 0x42, a, b, ..., bo]`. -/
theorem encodeBytes_sixty_six_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk bl bm bn bo :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj, bk, bl, bm, bn,
      bo] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x42, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj, bk, bl, bm, bn, bo] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Sixty-seven-byte long string:
    `encodeBytes [a, b, ..., bp] = [0xB8, 0x43, a, b, ..., bp]`. -/
theorem encodeBytes_sixty_seven_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk bl bm bn bo bp :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj, bk, bl, bm, bn,
      bo, bp] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x43, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj, bk, bl, bm, bn, bo, bp] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Sixty-eight-byte long string:
    `encodeBytes [a, b, ..., bq] = [0xB8, 0x44, a, b, ..., bq]`. -/
theorem encodeBytes_sixty_eight_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk bl bm bn bo bp bq :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj, bk, bl, bm, bn,
      bo, bp, bq] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x44, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj, bk, bl, bm, bn, bo, bp, bq] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Sixty-nine-byte long string:
    `encodeBytes [a, b, ..., br] = [0xB8, 0x45, a, b, ..., br]`. -/
theorem encodeBytes_sixty_nine_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk bl bm bn bo bp bq br :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj, bk, bl, bm, bn,
      bo, bp, bq, br] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x45, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj, bk, bl, bm, bn, bo, bp, bq, br] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Seventy-byte long string:
    `encodeBytes [a, b, ..., bs] = [0xB8, 0x46, a, b, ..., bs]`. -/
theorem encodeBytes_seventy_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk bl bm bn bo bp bq br bs :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj, bk, bl, bm, bn,
      bo, bp, bq, br, bs] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x46, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj, bk, bl, bm, bn, bo, bp, bq, br, bs] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Seventy-one-byte long string:
    `encodeBytes [a, b, ..., bt] = [0xB8, 0x47, a, b, ..., bt]`. -/
theorem encodeBytes_seventy_one_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk bl bm bn bo bp bq br bs bt :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj, bk, bl, bm, bn,
      bo, bp, bq, br, bs, bt] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x47, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj, bk, bl, bm, bn, bo, bp, bq, br, bs, bt] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Seventy-two-byte long string:
    `encodeBytes [a, b, ..., bu] = [0xB8, 0x48, a, b, ..., bu]`. -/
theorem encodeBytes_seventy_two_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk bl bm bn bo bp bq br bs bt bu :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj, bk, bl, bm, bn,
      bo, bp, bq, br, bs, bt, bu] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x48, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj, bk, bl, bm, bn, bo, bp, bq, br, bs, bt, bu] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Seventy-three-byte long string:
    `encodeBytes [a, b, ..., bv] = [0xB8, 0x49, a, b, ..., bv]`. -/
theorem encodeBytes_seventy_three_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk bl bm bn bo bp bq br bs bt bu bv :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj, bk, bl, bm, bn,
      bo, bp, bq, br, bs, bt, bu, bv] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x49, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj, bk, bl, bm, bn, bo, bp, bq, br, bs, bt, bu, bv] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Seventy-four-byte long string:
    `encodeBytes [a, b, ..., bw] = [0xB8, 0x4A, a, b, ..., bw]`. -/
theorem encodeBytes_seventy_four_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk bl bm bn bo bp bq br bs bt bu bv bw :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj, bk, bl, bm, bn,
      bo, bp, bq, br, bs, bt, bu, bv, bw] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x4A, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj, bk, bl, bm, bn, bo, bp, bq, br, bs, bt, bu, bv, bw] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Seventy-five-byte long string:
    `encodeBytes [a, b, ..., bx] = [0xB8, 0x4B, a, b, ..., bx]`. -/
theorem encodeBytes_seventy_five_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk bl bm bn bo bp bq br bs bt bu bv bw bx :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj, bk, bl, bm, bn,
      bo, bp, bq, br, bs, bt, bu, bv, bw, bx] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x4B, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj, bk, bl, bm, bn, bo, bp, bq, br, bs, bt, bu, bv, bw,
        bx] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Seventy-six-byte long string:
    `encodeBytes [a, b, ..., bz] = [0xB8, 0x4C, a, b, ..., bz]`. -/
theorem encodeBytes_seventy_six_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk bl bm bn bo bp bq br bs bt bu bv bw bx bz :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj, bk, bl, bm, bn,
      bo, bp, bq, br, bs, bt, bu, bv, bw, bx, bz] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x4C, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj, bk, bl, bm, bn, bo, bp, bq, br, bs, bt, bu, bv, bw,
        bx, bz] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Seventy-seven-byte long string:
    `encodeBytes [a, b, ..., ca] = [0xB8, 0x4D, a, b, ..., ca]`. -/
theorem encodeBytes_seventy_seven_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk bl bm bn bo bp bq br bs bt bu bv bw bx bz ca :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj, bk, bl, bm, bn,
      bo, bp, bq, br, bs, bt, bu, bv, bw, bx, bz, ca] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x4D, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj, bk, bl, bm, bn, bo, bp, bq, br, bs, bt, bu, bv, bw,
        bx, bz, ca] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Seventy-eight-byte long string:
    `encodeBytes [a, b, ..., cb] = [0xB8, 0x4E, a, b, ..., cb]`. -/
theorem encodeBytes_seventy_eight_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk bl bm bn bo bp bq br bs bt bu bv bw bx bz ca cb :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj, bk, bl, bm, bn,
      bo, bp, bq, br, bs, bt, bu, bv, bw, bx, bz, ca, cb] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x4E, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj, bk, bl, bm, bn, bo, bp, bq, br, bs, bt, bu, bv, bw,
        bx, bz, ca, cb] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Seventy-nine-byte long string:
    `encodeBytes [a, b, ..., cc] = [0xB8, 0x4F, a, b, ..., cc]`. -/
theorem encodeBytes_seventy_nine_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk bl bm bn bo bp bq br bs bt bu bv bw bx bz ca cb cc :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj, bk, bl, bm, bn,
      bo, bp, bq, br, bs, bt, bu, bv, bw, bx, bz, ca, cb, cc] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x4F, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj, bk, bl, bm, bn, bo, bp, bq, br, bs, bt, bu, bv, bw,
        bx, bz, ca, cb, cc] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Eighty-byte long string:
    `encodeBytes [a, b, ..., cd] = [0xB8, 0x50, a, b, ..., cd]`. -/
theorem encodeBytes_eighty_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk bl bm bn bo bp bq br bs bt bu bv bw bx bz ca cb cc cd :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj, bk, bl, bm, bn,
      bo, bp, bq, br, bs, bt, bu, bv, bw, bx, bz, ca, cb, cc, cd] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x50, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj, bk, bl, bm, bn, bo, bp, bq, br, bs, bt, bu, bv, bw,
        bx, bz, ca, cb, cc, cd] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Eighty-one-byte long string:
    `encodeBytes [a, b, ..., ce] = [0xB8, 0x51, a, b, ..., ce]`. -/
theorem encodeBytes_eighty_one_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk bl bm bn bo bp bq br bs bt bu bv bw bx bz ca cb cc cd ce :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj, bk, bl, bm, bn,
      bo, bp, bq, br, bs, bt, bu, bv, bw, bx, bz, ca, cb, cc, cd, ce] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x51, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj, bk, bl, bm, bn, bo, bp, bq, br, bs, bt, bu, bv, bw,
        bx, bz, ca, cb, cc, cd, ce] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Eighty-two-byte long string:
    `encodeBytes [a, b, ..., cf] = [0xB8, 0x52, a, b, ..., cf]`. -/
theorem encodeBytes_eighty_two_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk bl bm bn bo bp bq br bs bt bu bv bw bx bz ca cb cc cd ce cf :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj, bk, bl, bm, bn,
      bo, bp, bq, br, bs, bt, bu, bv, bw, bx, bz, ca, cb, cc, cd, ce, cf] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x52, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj, bk, bl, bm, bn, bo, bp, bq, br, bs, bt, bu, bv, bw,
        bx, bz, ca, cb, cc, cd, ce, cf] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Eighty-three-byte long string:
    `encodeBytes [a, b, ..., cg] = [0xB8, 0x53, a, b, ..., cg]`. -/
theorem encodeBytes_eighty_three_long
    (a b c d e f g h i j k l m n o p q r s t u v w x y z aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk bl bm bn bo bp bq br bs bt bu bv bw bx bz ca cb cc cd ce cf cg :
      Byte) :
    encodeBytes [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x,
      y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj, ak, al, am, an, ao, ap, aq, ar, as,
      au, av, aw, ax, ay, az, ba, bb, bc, bd, be, bf, bg, bh, bi, bj, bk, bl, bm, bn,
      bo, bp, bq, br, bs, bt, bu, bv, bw, bx, bz, ca, cb, cc, cd, ce, cf, cg] =
      [BitVec.ofNat 8 0xB8, BitVec.ofNat 8 0x53, a, b, c, d, e, f, g, h, i, j, k, l, m,
        n, o, p, q, r, s, t, u, v, w, x, y, z, aa, ab, ac, ad, ae, af, ag, ah, ai, aj,
        ak, al, am, an, ao, ap, aq, ar, as, au, av, aw, ax, ay, az, ba, bb, bc, bd,
        be, bf, bg, bh, bi, bj, bk, bl, bm, bn, bo, bp, bq, br, bs, bt, bu, bv, bw,
        bx, bz, ca, cb, cc, cd, ce, cf, cg] := by
  simp [encodeBytes, Nat.toBytesBE]

/-- Executable encoding example for the concrete 84-byte long-string payload. -/
theorem encodeBytes_eighty_four_long :
    encodeBytes rlpEightyFourBytePayload =
      [(0xB8 : Byte), (0x54 : Byte)] ++ rlpEightyFourBytePayload := by
  native_decide

/-- Executable encoding example for the concrete 85-byte long-string payload. -/
theorem encodeBytes_eighty_five_long :
    encodeBytes rlpEightyFiveBytePayload =
      [(0xB8 : Byte), (0x55 : Byte)] ++ rlpEightyFiveBytePayload := by
  native_decide

/-- Executable encoding example for the concrete 86-byte long-string payload. -/
theorem encodeBytes_eighty_six_long :
    encodeBytes rlpEightySixBytePayload =
      [(0xB8 : Byte), (0x56 : Byte)] ++ rlpEightySixBytePayload := by
  native_decide

/-- Executable encoding example for the concrete 87-byte long-string payload. -/
theorem encodeBytes_eighty_seven_long :
    encodeBytes rlpEightySevenBytePayload =
      [(0xB8 : Byte), (0x57 : Byte)] ++ rlpEightySevenBytePayload := by
  native_decide

/-- Executable encoding example for the concrete 88-byte long-string payload. -/
theorem encodeBytes_eighty_eight_long :
    encodeBytes rlpEightyEightBytePayload =
      [(0xB8 : Byte), (0x58 : Byte)] ++ rlpEightyEightBytePayload := by
  native_decide

/-- Executable encoding example for the concrete 89-byte long-string payload. -/
theorem encodeBytes_eighty_nine_long :
    encodeBytes rlpEightyNineBytePayload =
      [(0xB8 : Byte), (0x59 : Byte)] ++ rlpEightyNineBytePayload := by
  native_decide

/-- Executable encoding example for the concrete 90-byte long-string payload. -/
theorem encodeBytes_ninety_long :
    encodeBytes rlpNinetyBytePayload =
      [(0xB8 : Byte), (0x5A : Byte)] ++ rlpNinetyBytePayload := by
  native_decide

/-- Executable encoding example for the concrete 91-byte long-string payload. -/
theorem encodeBytes_ninety_one_long :
    encodeBytes rlpNinetyOneBytePayload =
      [(0xB8 : Byte), (0x5B : Byte)] ++ rlpNinetyOneBytePayload := by
  native_decide

/-- Executable encoding example for the concrete 92-byte long-string payload. -/
theorem encodeBytes_ninety_two_long :
    encodeBytes rlpNinetyTwoBytePayload =
      [(0xB8 : Byte), (0x5C : Byte)] ++ rlpNinetyTwoBytePayload := by
  native_decide

/-- Executable encoding example for the concrete 93-byte long-string payload. -/
theorem encodeBytes_ninety_three_long :
    encodeBytes rlpNinetyThreeBytePayload =
      [(0xB8 : Byte), (0x5D : Byte)] ++ rlpNinetyThreeBytePayload := by
  native_decide

/-- Executable encoding example for the concrete 94-byte long-string payload. -/
theorem encodeBytes_ninety_four_long :
    encodeBytes rlpNinetyFourBytePayload =
      [(0xB8 : Byte), (0x5E : Byte)] ++ rlpNinetyFourBytePayload := by
  native_decide

/-- Executable encoding example for the concrete 95-byte long-string payload. -/
theorem encodeBytes_ninety_five_long :
    encodeBytes rlpNinetyFiveBytePayload =
      [(0xB8 : Byte), (0x5F : Byte)] ++ rlpNinetyFiveBytePayload := by
  native_decide

/-- Executable encoding example for the concrete 96-byte long-string payload. -/
theorem encodeBytes_ninety_six_long :
    encodeBytes rlpNinetySixBytePayload =
      [(0xB8 : Byte), (0x60 : Byte)] ++ rlpNinetySixBytePayload := by
  native_decide

/-- Executable encoding example for the concrete 97-byte long-string payload. -/
theorem encodeBytes_ninety_seven_long :
    encodeBytes rlpNinetySevenBytePayload =
      [(0xB8 : Byte), (0x61 : Byte)] ++ rlpNinetySevenBytePayload := by
  native_decide

/-- Executable encoding example for the concrete 98-byte long-string payload. -/
theorem encodeBytes_ninety_eight_long :
    encodeBytes rlpNinetyEightBytePayload =
      [(0xB8 : Byte), (0x62 : Byte)] ++ rlpNinetyEightBytePayload := by
  native_decide

/-- Executable encoding example for the concrete 99-byte long-string payload. -/
theorem encodeBytes_ninety_nine_long :
    encodeBytes rlpNinetyNineBytePayload =
      [(0xB8 : Byte), (0x63 : Byte)] ++ rlpNinetyNineBytePayload := by
  native_decide

/-- Executable encoding example for the concrete 100-byte long-string payload. -/
theorem encodeBytes_one_hundred_long :
    encodeBytes rlpOneHundredBytePayload =
      [(0xB8 : Byte), (0x64 : Byte)] ++ rlpOneHundredBytePayload := by
  native_decide

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
