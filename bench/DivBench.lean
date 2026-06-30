/-
  bench/DivBench.lean — two-axis dynamic cost harness for `evm_div` / `evm_mod`.

  Runs the VERIFIED `step` semantics (EvmAsm.Rv64.Execution) on concrete inputs
  and reports, per divisor class:

    * steps   — dynamic instruction (cycle) count   [PRIMARY zkVM cost driver]
    * loads / stores / memOps — memory-traffic count [2nd axis: paging proxy]
    * dwords  — distinct 8-byte cells touched        [working-set size]
    * pages   — distinct 1 KiB data pages touched    [page-in/out proxy]
    * correct — result checked against `a / b`

  Cost-model rationale (Gassmann et al., arXiv:2508.17518v2, RISC0/SP1):
  dynamic instruction count is the primary, near-linear proving-cost driver;
  per-instruction cost is ~uniform ("division is not expensive"); memory is a
  complementary axis — a paged-in access is 1 cycle but a page-in/out ≈ 1130
  cycles. This harness surfaces both axes so the optimization objective can be
  the frequency-weighted (instructions + paging) cost, not instructions alone.

  Run:  lake env lean bench/DivBench.lean
  (needs `lake build EvmAsm.Evm64.DivMod.Program EvmAsm.Rv64.Execution EvmAsm.Evm64.Basic`)
-/
import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Rv64.Execution
import EvmAsm.Evm64.Basic

open EvmAsm.Rv64
open EvmAsm.Evm64

/-- i-th 64-bit little-endian limb of a 256-bit value. -/
def limbN (v : BitVec 256) (i : Nat) : Word := BitVec.ofNat 64 (v.toNat >>> (64 * i))

/-- Initial data memory: dividend `a` at sp+0..+24, divisor `b` at sp+32..+56,
    everything else (scratch) zero. -/
def mkMem (sp : Word) (a b : BitVec 256) (addr : Word) : Word :=
  let off := (addr - sp).toNat
  if off < 32 ∧ off % 8 = 0 then limbN a (off / 8)
  else if 32 ≤ off ∧ off < 64 ∧ off % 8 = 0 then limbN b ((off - 32) / 8)
  else 0

def spBase : Word := 0xa0001000

def mkState (prog : Program) (a b : BitVec 256) : MachineState :=
  { regs := fun r => if r = Reg.x12 then spBase else 0
  , mem  := mkMem spBase a b
  , code := loadProgram 0 prog
  , pc   := 0 }

/-- If `i` is a memory op, return `(isStore, address)`; else `none`.
    Address computation mirrors `EvmAsm.Rv64.step` (base reg is the first field
    for loads (`rd rs1`) and for stores (`rs1 rs2`)). -/
def classifyMem? (s : MachineState) : Option (Bool × Word) :=
  match s.code s.pc with
  | some (.LD  _ rs1 off) => some (false, s.getReg rs1 + signExtend12 off)
  | some (.LW  _ rs1 off) => some (false, s.getReg rs1 + signExtend12 off)
  | some (.LWU _ rs1 off) => some (false, s.getReg rs1 + signExtend12 off)
  | some (.LB  _ rs1 off) => some (false, s.getReg rs1 + signExtend12 off)
  | some (.LBU _ rs1 off) => some (false, s.getReg rs1 + signExtend12 off)
  | some (.LH  _ rs1 off) => some (false, s.getReg rs1 + signExtend12 off)
  | some (.LHU _ rs1 off) => some (false, s.getReg rs1 + signExtend12 off)
  | some (.SD  rs1 _ off) => some (true,  s.getReg rs1 + signExtend12 off)
  | some (.SW  rs1 _ off) => some (true,  s.getReg rs1 + signExtend12 off)
  | some (.SB  rs1 _ off) => some (true,  s.getReg rs1 + signExtend12 off)
  | some (.SH  rs1 _ off) => some (true,  s.getReg rs1 + signExtend12 off)
  | _ => none

structure Tally where
  steps   : Nat := 0
  loads   : Nat := 0
  stores  : Nat := 0
  dwords  : List Nat := []   -- distinct 8-byte cell indices (addr/8)
  pages   : List Nat := []   -- distinct 1 KiB page indices   (addr/1024)

def Tally.note (acc : Tally) : Option (Bool × Word) → Tally
  | none => acc
  | some (isStore, addr) =>
      let d := addr.toNat / 8
      let p := addr.toNat / 1024
      { acc with
        loads  := acc.loads  + (if isStore then 0 else 1)
      , stores := acc.stores + (if isStore then 1 else 0)
      , dwords := if acc.dwords.contains d then acc.dwords else d :: acc.dwords
      , pages  := if acc.pages.contains p then acc.pages else p :: acc.pages }

/-- Step until PC = `exitPC` (clean return), accumulating cost metrics. -/
def runTally (exitPC : Word) : Nat → MachineState → Tally → (Tally × Option MachineState)
  | 0,        _, acc => (acc, none)
  | fuel + 1, s, acc =>
    if s.pc = exitPC then (acc, some s)
    else
      let acc := acc.note (classifyMem? s)
      match step s with
      | none    => (acc, none)
      | some s' => runTally exitPC fuel s' { acc with steps := acc.steps + 1 }

def readResult (s : MachineState) : Nat :=
  (s.mem (spBase + 32)).toNat
  + (s.mem (spBase + 40)).toNat * 2^64
  + (s.mem (spBase + 48)).toNat * 2^128
  + (s.mem (spBase + 56)).toNat * 2^192

structure Report where
  steps   : Nat
  loads   : Nat
  stores  : Nat
  memOps  : Nat
  dwords  : Nat   -- distinct 8-byte cells touched (working-set size)
  pages   : Nat   -- distinct 1 KiB data pages touched
  ok      : Bool
  correct : Bool
  deriving Repr

def benchDiv (prog : Program) (a b : BitVec 256) : Report :=
  let exitPC : Word := BitVec.ofNat 64 1068
  match runTally exitPC 20000 (mkState prog a b) {} with
  | (acc, some s) =>
      let expected := if b == 0 then 0 else a.toNat / b.toNat
      { steps := acc.steps, loads := acc.loads, stores := acc.stores
      , memOps := acc.loads + acc.stores, dwords := acc.dwords.length
      , pages := acc.pages.length, ok := true, correct := readResult s = expected }
  | (acc, none) =>
      { steps := acc.steps, loads := acc.loads, stores := acc.stores
      , memOps := acc.loads + acc.stores, dwords := acc.dwords.length
      , pages := acc.pages.length, ok := false, correct := false }

-- Yoichi's benchmark inputs --------------------------------------------------
def num : BitVec 256 := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

#eval ("DIV bench#1  (b ~ 2^128, n=3)", benchDiv evm_div num 0x100000000000000000000000000000033)
#eval ("DIV bench#2  (b ~ 2^64,  n=2)", benchDiv evm_div num 0x10000000000000033)
#eval ("DIV b=2        (n=1 small)", benchDiv evm_div num 2)
#eval ("DIV b=7        (n=1 small)", benchDiv evm_div num 7)
#eval ("DIV b=2^64-1   (n=1 max)  ", benchDiv evm_div num 0xFFFFFFFFFFFFFFFF)
#eval ("DIV b full256  (n=4)      ", benchDiv evm_div num 0x8000000000000000000000000000000000000000000000000000000000000001)
