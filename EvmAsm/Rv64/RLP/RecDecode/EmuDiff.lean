/-
  TEMPORARY differential emulation: the flattened rlp_decode machine code
  (decProg at 0x1000 + rdbeProg at 0x1800) vs the spec decodeD.
  Not imported by any umbrella; built directly, then deleted or retained
  as a check module.
-/
import EvmAsm.Rv64.RLP.RecDecode.DecodeFn

namespace EvmAsm.Rv64.SAsm.RecDecode.EmuDiff

open EvmAsm.Rv64
open EvmAsm.EL.RLP (Byte RLPItem encode)
open EvmAsm.EL.RLP.Ref (decodeD win)
open EvmAsm.Rv64.SAsm.RecDecode

def inBase : Word := 0x4000
def fp0 : Word := 0x10000
def retAddr : Word := 0x3000

partial def runUntil (fuel : Nat) (s : MachineState) : Option MachineState :=
  match fuel with
  | 0 => none
  | f + 1 =>
    if s.pc = retAddr then some s
    else match step s with
      | none => none
      | some s' => runUntil f s'

def mkState (bs : List Byte) (len budget : Nat) : MachineState :=
  let s0 : MachineState := {
    regs := fun r =>
      if r = .x10 then inBase
      else if r = .x11 then BitVec.ofNat 64 len
      else if r = .x12 then BitVec.ofNat 64 budget
      else if r = .x13 then fp0
      else if r = .x1 then retAddr
      else 0
    mem := fun _ => 0
    code := decCr
    pc := decEntry }
  s0.writeBytesAsWords inBase bs

/-- Run the machine on `bs` (full window) at `budget`; return status or
    none on divergence/trap. -/
def machineStatus (bs : List Byte) (budget : Nat) : Option Word := do
  let s ← runUntil 200000 (mkState bs bs.length budget)
  some (s.regs .x10)

def specStatus (bs : List Byte) (budget : Nat) : Word :=
  if (decodeD budget ((bs.drop 0).take bs.length)).isSome then 0 else 1

-- corpus generators (as in RefDecodeFuzz)
def lcgNext (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407
def genBytes (n : Nat) (s : UInt64) : List Byte × UInt64 := Id.run do
  let mut out : List Byte := []
  let mut st := s
  for _ in [:n] do
    st := lcgNext st
    out := BitVec.ofNat 8 (st.toNat % 256) :: out
  return (out.reverse, st)
def lenPool : List Nat := [0, 1, 2, 3, 54, 55, 56, 57, 80]
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
        let nItems := (lcgNext s1).toNat % 4
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

def nested (depth : Nat) : List Byte := Id.run do
  let mut b : List Byte := [0xc0#8]
  for _ in [:depth - 1] do
    let n := b.length
    if n ≤ 55 then
      b := BitVec.ofNat 8 (0xC0 + n) :: b
  return b

def run : IO Unit := do
  let mut st : UInt64 := 2026
  let mut bad := 0
  let mut cases := 0
  -- 1. round-trip encodings at generous budget
  for _ in [:120] do
    let (item, st') := genItem 3 st
    st := st'
    let bs := encode item
    if bs.length ≤ 120 then
      cases := cases + 1
      let m := machineStatus bs 16
      let sp := specStatus bs 16
      if m ≠ some sp then
        bad := bad + 1
        IO.println s!"ENC MISMATCH: {repr bs} machine={repr m} spec={sp}"
  -- 2. biased random bytes
  for _ in [:250] do
    st := lcgNext st
    let n := (st.toNat % 10) + (if st.toNat % 7 == 0 then 50 else 0)
    let (bs, st') := genBiasedBytes n st
    st := st'
    cases := cases + 1
    let m := machineStatus bs 16
    let sp := specStatus bs 16
    if m ≠ some sp then
      bad := bad + 1
      IO.println s!"RAND MISMATCH: {repr bs} machine={repr m} spec={sp}"
  -- 3. mutations of valid encodings
  for _ in [:120] do
    let (item, st') := genItem 2 st
    st := st'
    let enc := encode item
    st := lcgNext st
    let pos := st.toNat % (enc.length + 1)
    st := lcgNext st
    let mutated := (enc.set pos (BitVec.ofNat 8 (st.toNat % 256)))
    for bs in [mutated, enc.take (enc.length - 1), enc ++ [0x05#8]] do
      if bs.length ≤ 120 then
        cases := cases + 1
        let m := machineStatus bs 16
        let sp := specStatus bs 16
        if m ≠ some sp then
          bad := bad + 1
          IO.println s!"MUT MISMATCH: {repr bs} machine={repr m} spec={sp}"
  -- 4. nesting depth vs budget (the cap behavior)
  for depth in [1, 2, 3, 5, 8] do
    for budget in [0, 1, 2, 3, 5, 8, 16] do
      let bs := nested depth
      cases := cases + 1
      let m := machineStatus bs budget
      let sp := specStatus bs budget
      if m ≠ some sp then
        bad := bad + 1
        IO.println s!"DEPTH MISMATCH depth={depth} budget={budget}: machine={repr m} spec={sp}"
  -- 5. empty input
  cases := cases + 1
  if machineStatus [] 16 ≠ some (specStatus [] 16) then
    bad := bad + 1
    IO.println "EMPTY MISMATCH"
  IO.println s!"MACHINE-SPEC DIFF: {cases} cases, {bad} mismatches"

#eval run

end EvmAsm.Rv64.SAsm.RecDecode.EmuDiff
