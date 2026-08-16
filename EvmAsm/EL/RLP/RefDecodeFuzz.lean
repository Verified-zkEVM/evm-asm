/-
  TEMPORARY differential fuzz: Ref.decode vs decodeFully.
  Not imported by any umbrella; built directly, then deleted.
-/
import EvmAsm.EL.RLP.RefDecode
import EvmAsm.EL.RLP.FullDecode

namespace EvmAsm.EL.RLP.RefDecodeFuzz

open EvmAsm.EL.RLP

def lcgNext (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

def genBytes (n : Nat) (s : UInt64) : List Byte × UInt64 := Id.run do
  let mut out : List Byte := []
  let mut st := s
  for _ in [:n] do
    st := lcgNext st
    out := BitVec.ofNat 8 (st.toNat % 256) :: out
  return (out.reverse, st)

def lenPool : List Nat := [0, 1, 2, 3, 54, 55, 56, 57, 100]

/-- boundary-biased byte pool: header-shaped bytes appear often. -/
def bytePool : List Nat :=
  [0x00, 0x01, 0x7f, 0x80, 0x81, 0xb7, 0xb8, 0xb9, 0xbf, 0xc0, 0xc1, 0xf7, 0xf8, 0xff]

def genBiasedBytes (n : Nat) (s : UInt64) : List Byte × UInt64 := Id.run do
  let mut out : List Byte := []
  let mut st := s
  for _ in [:n] do
    st := lcgNext st
    let r := st.toNat % (2 * bytePool.length)
    let b := if r < bytePool.length then bytePool[r]! else (lcgNext st).toNat % 256
    out := BitVec.ofNat 8 b :: out
  return (out.reverse, st)

instance : Inhabited RLPItem := ⟨.bytes []⟩

partial def genItem : Nat → UInt64 → RLPItem × UInt64
  | 0, s =>
      let s1 := lcgNext s
      let len := lenPool[s1.toNat % lenPool.length]!
      let (bs, s2) := genBytes len s1
      (.bytes bs, s2)
  | depth + 1, s =>
      let s1 := lcgNext s
      if s1.toNat % 5 == 0 then
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

def run : IO Unit := do
  let mut st : UInt64 := 42
  let mut bad := 0
  -- 1. round-trip: Ref.decode (encode x) = some x
  for i in [:3000] do
    let (item, st') := genItem 3 st
    st := st'
    if Ref.decode (encode item) ≠ some item then
      bad := bad + 1
      IO.println s!"ROUNDTRIP MISMATCH at {i}: {repr item}"
  -- 2. arbitrary/boundary bytes: Ref.decode bs = decodeFully bs
  for i in [:20000] do
    st := lcgNext st
    let n := (st.toNat % 12) + (if st.toNat % 7 == 0 then 50 else 0)
    let (bs, st') := genBiasedBytes n st
    st := st'
    if Ref.decode bs ≠ decodeFully bs then
      bad := bad + 1
      IO.println s!"DIFF MISMATCH at {i}: bytes {repr bs} ref={repr (Ref.decode bs)} full={repr (decodeFully bs)}"
  -- 3. mutated valid encodings (near-miss inputs)
  for i in [:3000] do
    let (item, st') := genItem 3 st
    st := st'
    let enc := encode item
    st := lcgNext st
    let pos := st.toNat % (enc.length + 1)
    st := lcgNext st
    let newByte := BitVec.ofNat 8 (st.toNat % 256)
    let mutated := enc.set pos newByte
    if Ref.decode mutated ≠ decodeFully mutated then
      bad := bad + 1
      IO.println s!"MUTATE MISMATCH at {i}: bytes {repr mutated}"
    -- also truncations and extensions
    let trunc := enc.take (enc.length - 1)
    if Ref.decode trunc ≠ decodeFully trunc then
      bad := bad + 1
      IO.println s!"TRUNC MISMATCH at {i}: bytes {repr trunc}"
    let ext := enc ++ [newByte]
    if Ref.decode ext ≠ decodeFully ext then
      bad := bad + 1
      IO.println s!"EXT MISMATCH at {i}: bytes {repr ext}"
  if bad == 0 then
    IO.println "REF-DECODE FUZZ: all cases agree"
  else
    IO.println s!"REF-DECODE FUZZ: {bad} mismatches"

#eval run

end EvmAsm.EL.RLP.RefDecodeFuzz
