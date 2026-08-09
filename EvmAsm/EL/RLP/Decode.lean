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

Both `decodeAux` and `decodeItems` structurally recurse on `nDepth`.
Each nested item decode consumes 2 units of `nDepth` (one in `decodeAux`, one
in `decodeItems`), so we use `2 * bs.length` as the initial `nDepth`.

`2 * bs.length` is a termination measure for Lean, not an RLP depth policy.
The reference `ethereum-rlp` decoder has no corresponding input-derived fuel:
on sufficiently deep nesting CPython raises `RecursionError` (at roughly its
recursion limit), which is not a `DecodingError` and is not converted into an
`InvalidBlock` result.  The reference therefore becomes undefined/crashes on
that path, while this port returns `none`; that divergence is deliberate and
one-directional: we reject where the reference is undefined, and never accept
an input that the reference rejects.

The zero-fuel arm is unreachable from the top-level `decode` wrapper by
construction, rather than being an omitted behavioural case.  The order in
`decodeItems` is load-bearing: it matches `bs` before `nDepth`, so an empty
remainder returns `some ([], [])` without testing fuel, and only a nonempty
remainder can reach the zero case.  Every recursive item consumes at least one
byte and two fuel units, while the wrapper starts with two units per input
byte.  Thus `decodeAux 0` can only be reached by an out-of-contract direct call,
not by an input handed to `decode`.  This is the same distinction recorded by
the MPT fuel precedents: `IncrementalMpt`'s `decodeFuel` over-approximates an
acyclic walk (`decodeFuel` docstring), and `IncrementalMptWrite` explicitly
classifies reachable exhaustion as rejection while documenting unreachable
encoding exhaustion.  RLP is the third such fuelled decoder and its exhaustion
branch is theoretical, not a guest input case.  The guest's separate 1024
active-list depth cap and status-7 rejection are the reachable bound described
in #11776; this model fuel is not that cap. -/

mutual
/-- Decode one RLP item from the byte stream. -/
def decodeAux (nDepth : Nat) (bs : List Byte) : Option (RLPItem × List Byte) :=
  match nDepth with
  | 0 => none
  | nDepth + 1 =>
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
         let (items, leftover) ← decodeItems nDepth payload
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
           let (items, leftover) ← decodeItems nDepth payload
           if List.isEmpty leftover then some (.list items, rest'')
           else none

/-- Decode consecutive items from a byte stream until empty. -/
def decodeItems (nDepth : Nat) (bs : List Byte) : Option (List RLPItem × List Byte) :=
  match bs with
  | [] => some ([], [])
  | _ =>
    match nDepth with
    | 0 => none
    | nDepth + 1 => do
      let (item, rest) ← decodeAux nDepth bs
      let (items, rest') ← decodeItems nDepth rest
      some (item :: items, rest')
end

/-- Decode one RLP item from the front of a byte stream. -/
def decode (bs : List Byte) : Option (RLPItem × List Byte) :=
  decodeAux (2 * bs.length) bs

/-- Expose the exact nDepth budget used by the top-level decode wrapper. -/
theorem decode_eq_decodeAux_length (bs : List Byte) :
    decode bs = decodeAux (2 * bs.length) bs := by
  rfl

/-- Top-level decode on a nonempty stream uses two nDepth units for the head byte
    plus twice the tail length. -/
theorem decode_cons_eq_decodeAux_fuel (pfx : Byte) (rest : List Byte) :
    decode (pfx :: rest) = decodeAux (2 * rest.length + 2) (pfx :: rest) := by
  unfold decode
  simp [Nat.mul_succ]

end EvmAsm.EL.RLP
