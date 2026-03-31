/-
  EvmAsm.EL.RLP.Decode

  RLP decoding with canonical form enforcement.
  Reference: Ethereum Yellow Paper, Appendix B.
-/
import EvmAsm.EL.RLP.Basic

namespace EvmAsm.EL.RLP

/-! ## Helpers -/

/-- Take exactly `n` bytes from the front of `bs`. Returns `none` if too short. -/
def takeBytes (bs : List Byte) (n : Nat) : Option (List Byte × List Byte) :=
  if bs.length ≥ n then some (bs.take n, bs.drop n)
  else none

/-- Decode a big-endian length from the first `n` bytes.
    Rejects leading zeros (canonical encoding). -/
def readLength (bs : List Byte) (n : Nat) : Option (Nat × List Byte) := do
  let (lenBytes, rest) ← takeBytes bs n
  match lenBytes with
  | [] => some (0, rest)
  | b :: _ =>
    if lenBytes.length > 1 && b == (0 : Byte) then none
    else some (Nat.fromBytesBE lenBytes, rest)

/-! ## Decoding

Both `decodeAux` and `decodeItems` structurally recurse on `fuel`.
Each item decode consumes 2 units of fuel (one in `decodeAux`, one in
`decodeItems`), so we use `2 * bs.length` as the initial fuel. -/

mutual
/-- Decode one RLP item from the byte stream. -/
def decodeAux (fuel : Nat) (bs : List Byte) : Option (RLPItem × List Byte) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
  match bs with
  | [] => none
  | pfx :: rest =>
    let p := pfx.toNat
    if p < 0x80 then
      -- Single byte [0x00..0x7F]
      some (.bytes [pfx], rest)
    else if p ≤ 0xB7 then
      -- Short byte string: prefix = 0x80 + len
      let len := p - 0x80
      do let (data, rest') ← takeBytes rest len
         -- Canonical: single byte < 0x80 must use single-byte form
         match data with
         | [b] => if b.toNat < 0x80 then none else some (.bytes data, rest')
         | _ => some (.bytes data, rest')
    else if p ≤ 0xBF then
      -- Long byte string: prefix = 0xB7 + lenLen
      let lenLen := p - 0xB7
      do let (lenVal, rest') ← readLength rest lenLen
         -- Canonical: must not use long form for length ≤ 55
         if lenVal ≤ 55 then none
         else do
           let (data, rest'') ← takeBytes rest' lenVal
           some (.bytes data, rest'')
    else if p ≤ 0xF7 then
      -- Short list: prefix = 0xC0 + len
      let len := p - 0xC0
      do let (payload, rest') ← takeBytes rest len
         let (items, leftover) ← decodeItems fuel payload
         if List.isEmpty leftover then some (.list items, rest')
         else none
    else
      -- Long list: prefix = 0xF7 + lenLen
      let lenLen := p - 0xF7
      do let (lenVal, rest') ← readLength rest lenLen
         -- Canonical: must not use long form for length ≤ 55
         if lenVal ≤ 55 then none
         else do
           let (payload, rest'') ← takeBytes rest' lenVal
           let (items, leftover) ← decodeItems fuel payload
           if List.isEmpty leftover then some (.list items, rest'')
           else none

/-- Decode consecutive items from a byte stream until empty. -/
def decodeItems (fuel : Nat) (bs : List Byte) : Option (List RLPItem × List Byte) :=
  match bs with
  | [] => some ([], [])
  | _ =>
    match fuel with
    | 0 => none
    | fuel + 1 => do
      let (item, rest) ← decodeAux fuel bs
      let (items, rest') ← decodeItems fuel rest
      some (item :: items, rest')
end

/-- Decode one RLP item from the front of a byte stream. -/
def decode (bs : List Byte) : Option (RLPItem × List Byte) :=
  decodeAux (2 * bs.length) bs

end EvmAsm.EL.RLP
