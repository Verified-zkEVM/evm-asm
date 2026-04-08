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
  | .x5  => regidx.Regidx 5
  | .x6  => regidx.Regidx 6
  | .x7  => regidx.Regidx 7
  | .x10 => regidx.Regidx 10
  | .x11 => regidx.Regidx 11
  | .x12 => regidx.Regidx 12

-- ============================================================================
-- Register mapping: Rv64.Reg → Register (SAIL state key, for non-x0)
-- ============================================================================

/-- Map an Rv64 non-x0 register to its SAIL Register key.
    x0 has no entry in the state (hardwired zero). -/
def regToSailReg : Reg → Option Register
  | .x0  => none
  | .x1  => some Register.x1
  | .x2  => some Register.x2
  | .x5  => some Register.x5
  | .x6  => some Register.x6
  | .x7  => some Register.x7
  | .x10 => some Register.x10
  | .x11 => some Register.x11
  | .x12 => some Register.x12

/-- Pure register lookup: read an integer register value from SAIL state.
    Returns 0 for x0, or looks up in the ExtDHashMap for others.
    Each case is concrete so Lean knows RegisterType Register.xN = BitVec 64. -/
noncomputable def sailRegVal (s : SailState) (r : Reg) : Option (BitVec 64) :=
  match r with
  | .x0  => some 0#64  -- x0 is hardwired zero
  | .x1  => s.regs.get? Register.x1
  | .x2  => s.regs.get? Register.x2
  | .x5  => s.regs.get? Register.x5
  | .x6  => s.regs.get? Register.x6
  | .x7  => s.regs.get? Register.x7
  | .x10 => s.regs.get? Register.x10
  | .x11 => s.regs.get? Register.x11
  | .x12 => s.regs.get? Register.x12

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
structure StateRel (s_rv : MachineState) (s_sail : SailState) : Prop where
  /-- Registers agree on the 9-register subset. -/
  reg_agree : ∀ (r : Reg), sailRegVal s_sail r = some (s_rv.getReg r)
  /-- Memory agrees: SAIL bytes reconstruct to Rv64 doublewords. -/
  mem_agree : ∀ (a : BitVec 64),
    reconstructDword s_sail.mem a.toNat = s_rv.getMem a

end EvmAsm.Rv64.SailEquiv
