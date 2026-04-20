/-
  EvmAsm.Rv64.SailEquiv.StateRel

  Abstraction relation between the simplified Rv64 MachineState
  and the SAIL-generated RISC-V formal spec state.
-/

import EvmAsm.Rv64.Basic
import LeanRV64D

open LeanRV64D.Functions
open Sail

namespace EvmAsm.Rv64.SailEquiv

-- ============================================================================
-- Type abbreviations
-- ============================================================================

/-- The SAIL machine state type. -/
abbrev SailState := PreSail.SequentialState RegisterType trivialChoiceSource

-- ============================================================================
-- Register mapping: Rv64.Reg → regidx (5-bit index)
-- ============================================================================

/-- Map Rv64.Reg to the SAIL 5-bit register index. -/
def regToRegidx : Reg → regidx
  | .x0  => regidx.Regidx 0
  | .x1  => regidx.Regidx 1
  | .x2  => regidx.Regidx 2
  | .x3  => regidx.Regidx 3
  | .x4  => regidx.Regidx 4
  | .x5  => regidx.Regidx 5
  | .x6  => regidx.Regidx 6
  | .x7  => regidx.Regidx 7
  | .x8  => regidx.Regidx 8
  | .x9  => regidx.Regidx 9
  | .x10 => regidx.Regidx 10
  | .x11 => regidx.Regidx 11
  | .x12 => regidx.Regidx 12
  | .x13 => regidx.Regidx 13
  | .x14 => regidx.Regidx 14
  | .x15 => regidx.Regidx 15
  | .x16 => regidx.Regidx 16
  | .x17 => regidx.Regidx 17
  | .x18 => regidx.Regidx 18
  | .x19 => regidx.Regidx 19
  | .x20 => regidx.Regidx 20
  | .x21 => regidx.Regidx 21
  | .x22 => regidx.Regidx 22
  | .x23 => regidx.Regidx 23
  | .x24 => regidx.Regidx 24
  | .x25 => regidx.Regidx 25
  | .x26 => regidx.Regidx 26
  | .x27 => regidx.Regidx 27
  | .x28 => regidx.Regidx 28
  | .x29 => regidx.Regidx 29
  | .x30 => regidx.Regidx 30
  | .x31 => regidx.Regidx 31

-- ============================================================================
-- Register mapping: Rv64.Reg → Register (SAIL state key, for non-x0)
-- ============================================================================

/-- Map an Rv64 non-x0 register to its SAIL Register key.
    x0 has no entry in the state (hardwired zero). -/
def regToSailReg : Reg → Option Register
  | .x0  => none
  | .x1  => some Register.x1
  | .x2  => some Register.x2
  | .x3  => some Register.x3
  | .x4  => some Register.x4
  | .x5  => some Register.x5
  | .x6  => some Register.x6
  | .x7  => some Register.x7
  | .x8  => some Register.x8
  | .x9  => some Register.x9
  | .x10 => some Register.x10
  | .x11 => some Register.x11
  | .x12 => some Register.x12
  | .x13 => some Register.x13
  | .x14 => some Register.x14
  | .x15 => some Register.x15
  | .x16 => some Register.x16
  | .x17 => some Register.x17
  | .x18 => some Register.x18
  | .x19 => some Register.x19
  | .x20 => some Register.x20
  | .x21 => some Register.x21
  | .x22 => some Register.x22
  | .x23 => some Register.x23
  | .x24 => some Register.x24
  | .x25 => some Register.x25
  | .x26 => some Register.x26
  | .x27 => some Register.x27
  | .x28 => some Register.x28
  | .x29 => some Register.x29
  | .x30 => some Register.x30
  | .x31 => some Register.x31

/-- Pure register lookup: read an integer register value from SAIL state.
    Returns 0 for x0, or looks up in the ExtDHashMap for others.
    Each case is concrete so Lean knows RegisterType Register.xN = BitVec 64. -/
noncomputable def sailRegVal (s : SailState) (r : Reg) : Option (BitVec 64) :=
  match r with
  | .x0  => some 0#64  -- x0 is hardwired zero
  | .x1  => s.regs.get? Register.x1
  | .x2  => s.regs.get? Register.x2
  | .x3  => s.regs.get? Register.x3
  | .x4  => s.regs.get? Register.x4
  | .x5  => s.regs.get? Register.x5
  | .x6  => s.regs.get? Register.x6
  | .x7  => s.regs.get? Register.x7
  | .x8  => s.regs.get? Register.x8
  | .x9  => s.regs.get? Register.x9
  | .x10 => s.regs.get? Register.x10
  | .x11 => s.regs.get? Register.x11
  | .x12 => s.regs.get? Register.x12
  | .x13 => s.regs.get? Register.x13
  | .x14 => s.regs.get? Register.x14
  | .x15 => s.regs.get? Register.x15
  | .x16 => s.regs.get? Register.x16
  | .x17 => s.regs.get? Register.x17
  | .x18 => s.regs.get? Register.x18
  | .x19 => s.regs.get? Register.x19
  | .x20 => s.regs.get? Register.x20
  | .x21 => s.regs.get? Register.x21
  | .x22 => s.regs.get? Register.x22
  | .x23 => s.regs.get? Register.x23
  | .x24 => s.regs.get? Register.x24
  | .x25 => s.regs.get? Register.x25
  | .x26 => s.regs.get? Register.x26
  | .x27 => s.regs.get? Register.x27
  | .x28 => s.regs.get? Register.x28
  | .x29 => s.regs.get? Register.x29
  | .x30 => s.regs.get? Register.x30
  | .x31 => s.regs.get? Register.x31

-- ============================================================================
-- Running SAIL computations
-- ============================================================================

/-- Run a SAIL monadic computation, returning the result and final state (or none on error). -/
noncomputable def runSail (m : SailM α) (s : SailState) : Option (α × SailState) :=
  match m s with
  | .ok v s' => some (v, s')
  | .error _ _ => none

-- ============================================================================
-- Memory reconstruction: SAIL byte-addressed → Rv64 doubleword-addressed
-- ============================================================================

/-- Reconstruct a 64-bit doubleword from 8 consecutive bytes in SAIL memory (little-endian). -/
def reconstructDword (mem : Std.ExtHashMap Nat (BitVec 8)) (addr : Nat) : BitVec 64 :=
  let b0 := (mem.getD addr 0).zeroExtend 64
  let b1 := (mem.getD (addr + 1) 0).zeroExtend 64
  let b2 := (mem.getD (addr + 2) 0).zeroExtend 64
  let b3 := (mem.getD (addr + 3) 0).zeroExtend 64
  let b4 := (mem.getD (addr + 4) 0).zeroExtend 64
  let b5 := (mem.getD (addr + 5) 0).zeroExtend 64
  let b6 := (mem.getD (addr + 6) 0).zeroExtend 64
  let b7 := (mem.getD (addr + 7) 0).zeroExtend 64
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) |||
  (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)

-- ============================================================================
-- State abstraction relation (no PC — proved separately at step level)
-- ============================================================================

/-- The abstraction relation between Rv64.MachineState and SAIL state.
    Asserts register and memory agreement only. -/
structure StateRel (sRv : MachineState) (sSail : SailState) : Prop where
  /-- Registers agree on all 32 integer registers. -/
  reg_agree : ∀ (r : Reg), sailRegVal sSail r = some (sRv.getReg r)
  /-- Memory agrees: SAIL bytes reconstruct to Rv64 doublewords. -/
  mem_agree : ∀ (a : BitVec 64),
    reconstructDword sSail.mem a.toNat = sRv.getMem a

end EvmAsm.Rv64.SailEquiv
