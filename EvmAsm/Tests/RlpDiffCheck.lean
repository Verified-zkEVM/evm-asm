/-
  EvmAsm.Tests.RlpDiffCheck

  RLP correctness test for the pure spec (`EvmAsm.EL.RLP`). RLP is a known
  common source of bugs, especially on UNTRUSTED input (see issue #9373); this
  binary pins the (proven self-consistent) spec to the canonical Ethereum
  standard and fuzzes its accept/reject behavior on arbitrary bytes.

  Two layers, mirroring `EvmAsm/Tests/ArithDiffCheck.lean`:

  * Official vectors (authoritative oracle): the vendored `ethereum/tests`
    RLP vectors (`tests/rlp-vectors/{valid,invalid}.txt`, refreshed by
    `scripts/fetch-rlp-test-vectors.sh`). For every VALID vector the canonical
    bytes must `decodeFully` to an item that re-`encode`s to exactly those bytes;
    for every INVALID vector `decodeFully` must REJECT (`none`). This is the only
    place the spec is tied to the real RLP standard rather than to itself.

  * Fuzz (oracle-free self-consistency, the untrusted-input net): random
    `RLPItem` trees must round-trip (`decodeFully (encode x) = some x`), and —
    the key untrusted-input check — for ARBITRARY/boundary/malformed bytes,
    `decodeFully bs` must be `none` OR decode to an item whose canonical
    re-encoding equals `bs` (the decoder must never accept non-canonical input).

  This module lives under `EvmAsm/Tests/` and is consumed only by the
  `rlp-diff-check` exe; it is never imported into any proof / the trusted base.
  Run via `lake exe rlp-diff-check` (see `scripts/rlp-check-all.sh`).
-/

import EvmAsm.EL.RLP.ByteStringDecodeBridge
import EvmAsm.EL.RLP.FullDecode
import EvmAsm.EL.RLP.ListDecode
import EvmAsm.EL.RLP.ListDecodeBridge
import EvmAsm.EL.RLP.LongForm
import EvmAsm.EL.RLP.LongFormDecodeBridge
import EvmAsm.EL.RLP.Prefix
import EvmAsm.EL.RLP.PrefixDecode
import EvmAsm.EL.RLP.Program
import EvmAsm.EL.RLP.ProgramSpec
import EvmAsm.EL.RLP.Properties
import EvmAsm.EL.RLP.ReadLength
import EvmAsm.EL.RLP.ReadLengthBridge
import EvmAsm.EL.RLP.Scalar

namespace EvmAsm.Tests.RlpDiffCheck

open EvmAsm.EL.RLP

-- ============================================================================
-- Hex <-> bytes (vector interchange; no external deps)
-- ============================================================================

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Parse a (no-`0x`) even-length hex string into bytes. -/
def parseHexBytes (s : String) : Option (List Byte) :=
  let cs0 := s.toList
  let cs := match cs0 with | '0' :: 'x' :: r => r | r => r
  let rec go : List Char → Option (List Byte)
    | [] => some []
    | [_] => none
    | a :: b :: r => do
        let hi ← hexDigit? a
        let lo ← hexDigit? b
        let rest ← go r
        some (BitVec.ofNat 8 (hi * 16 + lo) :: rest)
  go cs

def byteHex (b : Byte) : String :=
  let n := b.toNat
  let d (k : Nat) : Char := "0123456789abcdef".toList[k]!
  String.ofList [d (n / 16), d (n % 16)]

def bytesToHex (bs : List Byte) : String := String.join (bs.map byteHex)

-- ============================================================================
-- Deterministic generation (boundary-biased)
-- ============================================================================

/-- 64-bit LCG (Knuth MMIX constants); no external randomness. -/
def lcgNext (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- Generate `n` pseudo-random bytes; returns the bytes and advanced seed. -/
def genBytes (n : Nat) (s : UInt64) : List Byte × UInt64 := Id.run do
  let mut out : List Byte := []
  let mut st := s
  for _ in [:n] do
    st := lcgNext st
    out := BitVec.ofNat 8 (st.toNat % 256) :: out
  return (out.reverse, st)

/-- Byte-string lengths that exercise the RLP form boundaries. -/
def lenPool : List Nat := [0, 1, 2, 3, 54, 55, 56, 57, 100]

/-- Generate a random `RLPItem` of bounded depth. Lists stay small; byte
    lengths are biased toward the short/long-form boundary. -/
def genItem : Nat → UInt64 → RLPItem × UInt64
  | 0, s =>
      let s1 := lcgNext s
      let len := lenPool[s1.toNat % lenPool.length]!
      let (bs, s2) := genBytes len s1
      (.bytes bs, s2)
  | depth + 1, s =>
      let s1 := lcgNext s
      if s1.toNat % 5 == 0 then
        -- a list of 0..4 sub-items (each one level shallower)
        let nItems := (lcgNext s1).toNat % 5
        Id.run do
          let mut items : List RLPItem := []
          let mut st := lcgNext s1
          for _ in [:nItems] do
            let (it, st') := genItem depth st
            items := it :: items
            st := st'
          return (.list items.reverse, st)
      else
        let len := lenPool[s1.toNat % lenPool.length]!
        let (bs, s2) := genBytes len s1
        (.bytes bs, s2)

/-- Curated boundary / malformed byte buffers for the untrusted-input fuzz
    (in addition to random draws). Non-canonical entries must be rejected. -/
def boundaryBytes : List (List Byte) :=
  ([ []                                   -- empty (reject)
   , [0x00], [0x7f], [0x80], [0x81], [0xff]
   , [0x81, 0x00]                         -- non-canonical: 0x00 as string (reject)
   , [0x81, 0x7f]                         -- non-canonical: <0x80 as string (reject)
   , [0x82, 0x00, 0x01]                   -- leading-zero-ish 2-byte string (valid bytes)
   , [0xb8, 0x00]                         -- long form len 0 (reject: ≤55)
   , [0xb8, 0x37]                         -- long form len 55 (reject: must be short)
   , [0xc0]                               -- empty list
   , [0xc1, 0x00]                         -- list [0x00]
   , [0xf8, 0x00]                         -- long list len 0 (reject)
   , [0x83, 0x61, 0x62]                   -- declared 3, only 2 (reject: too short)
   ].map (fun l => l.map (BitVec.ofNat 8)))

-- ============================================================================
-- Checks
-- ============================================================================

inductive Fail where
  | vecValid (name hx : String) (note : String)
  | vecInvalid (name hx : String)
  | roundTrip (hx : String)
  | nonCanonical (hx reenc : String)

def Fail.render : Fail → String
  | .vecValid n hx note => s!"  [valid-vector {n}] 0x{hx}: {note}"
  | .vecInvalid n hx => s!"  [invalid-vector {n}] 0x{hx}: spec ACCEPTED a malformed encoding (should reject)"
  | .roundTrip hx => s!"  [round-trip] item encoding 0x{hx} did not decodeFully back to itself"
  | .nonCanonical hx re => s!"  [non-canonical] decodeFully accepted 0x{hx} but re-encodes to 0x{re}"

/-- A valid vector must decodeFully and re-encode to the same canonical bytes. -/
def checkValid (name : String) (bs : List Byte) : Option Fail :=
  match decodeFully bs with
  | none => some (.vecValid name (bytesToHex bs) "decodeFully returned none (should decode)")
  | some item =>
      if encode item == bs then none
      else some (.vecValid name (bytesToHex bs)
        s!"re-encodes to 0x{bytesToHex (encode item)} (not canonical / wrong)")

/-- An invalid vector must be rejected by decodeFully. -/
def checkInvalid (name : String) (bs : List Byte) : Option Fail :=
  match decodeFully bs with
  | none => none
  | some _ => some (.vecInvalid name (bytesToHex bs))

/-- Round-trip: a generated item must decode back to itself. -/
def checkRoundTrip (item : RLPItem) : Option Fail :=
  let enc := encode item
  if decodeFully enc == some item then none
  else some (.roundTrip (bytesToHex enc))

/-- Untrusted-input self-consistency: any bytes the decoder ACCEPTS must
    re-encode to exactly themselves (canonical). Rejection is always fine. -/
def checkNonCanonical (bs : List Byte) : Option Fail :=
  match decodeFully bs with
  | none => none
  | some item =>
      if encode item == bs then none
      else some (.nonCanonical (bytesToHex bs) (bytesToHex (encode item)))

-- ============================================================================
-- Runners
-- ============================================================================

def readVectorFile (path : String) : IO (List (String × List Byte)) := do
  if !(← System.FilePath.pathExists path) then
    IO.eprintln s!"rlp-diff-check: vector file not found: {path} (run scripts/fetch-rlp-test-vectors.sh)"
    return []
  let content ← IO.FS.readFile path
  let mut out : List (String × List Byte) := []
  for line in content.splitOn "\n" do
    match line.splitOn " " with
    | [name, hx] =>
        match parseHexBytes hx with
        | some bs => out := (name, bs) :: out
        | none => IO.eprintln s!"rlp-diff-check: bad hex for {name}: {hx}"
    | _ => pure ()   -- blank / malformed line
  return out.reverse

def runVectors (dir : String) : IO (Array Fail) := do
  let valid ← readVectorFile s!"{dir}/valid.txt"
  let invalid ← readVectorFile s!"{dir}/invalid.txt"
  IO.println s!"rlp-diff-check: {valid.length} valid + {invalid.length} invalid official vectors"
  let mut fails : Array Fail := #[]
  for (n, bs) in valid do
    match checkValid n bs with | some f => fails := fails.push f | none => pure ()
  for (n, bs) in invalid do
    match checkInvalid n bs with | some f => fails := fails.push f | none => pure ()
  return fails

def runFuzz (nItems nBytes : Nat) (seed : UInt64) : Array Fail := Id.run do
  let mut fails : Array Fail := #[]
  let mut s := if seed = 0 then 1 else seed
  -- round-trip over random items (depth up to 3)
  for _ in [:nItems] do
    let (item, s') := genItem 3 s
    s := s'
    match checkRoundTrip item with | some f => fails := fails.push f | none => pure ()
  -- non-canonical / untrusted-input self-consistency over the curated pool ...
  for bs in boundaryBytes do
    match checkNonCanonical bs with | some f => fails := fails.push f | none => pure ()
  -- ... and over random byte buffers of varied length
  for _ in [:nBytes] do
    let s1 := lcgNext s
    let len := s1.toNat % 40
    let (bs, s2) := genBytes len s1
    s := s2
    match checkNonCanonical bs with | some f => fails := fails.push f | none => pure ()
  return fails

def report (label : String) (fails : Array Fail) : IO Unit := do
  IO.println s!"FAIL: {fails.size} {label} mismatch(es):"
  for f in fails do IO.println f.render

def parseNat (s : String) (d : Nat) : Nat := s.toNat?.getD d
def parseSeed (s : String) (d : UInt64) : UInt64 := (s.toNat?.map UInt64.ofNat).getD d

def defaultVecDir : String := "tests/rlp-vectors"

def main (args : List String) : IO UInt32 := do
  match args with
  | "vectors" :: rest => do
      let dir := rest[0]?.getD defaultVecDir
      let fails ← runVectors dir
      if fails.size = 0 then
        IO.println "PASS: all official RLP vectors decode/reject as expected."; return 0
      report "vector" fails; return 1
  | "fuzz" :: rest => do
      let nItems := parseNat (rest[0]?.getD "") 50000
      let nBytes := parseNat (rest[1]?.getD "") 50000
      let seed := parseSeed (rest[2]?.getD "") 42
      let fails := runFuzz nItems nBytes seed
      if fails.size = 0 then
        IO.println s!"PASS: fuzz, nItems={nItems} nBytes={nBytes} seed={seed}"; return 0
      report "fuzz" fails; return 1
  | _ => do
      -- default: official vectors + a fuzz pass
      let nItems := parseNat (args[0]?.getD "") 50000
      let nBytes := parseNat (args[1]?.getD "") 50000
      let seed := parseSeed (args[2]?.getD "") 42
      let vfails ← runVectors defaultVecDir
      let ffails := runFuzz nItems nBytes seed
      let total := vfails.size + ffails.size
      if total = 0 then
        IO.println s!"PASS: official vectors + fuzz (nItems={nItems} nBytes={nBytes} seed={seed})."
        return 0
      if vfails.size > 0 then report "vector" vfails
      if ffails.size > 0 then report "fuzz" ffails
      return 1

end EvmAsm.Tests.RlpDiffCheck
