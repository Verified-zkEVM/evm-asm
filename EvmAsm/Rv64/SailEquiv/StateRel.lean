/-
  EvmAsm.Rv64.SailEquiv.StateRel

  Abstraction relation between the simplified Rv64 MachineState
  and the SAIL-generated RISC-V formal spec state.
-/

import EvmAsm.Rv64.Basic
import LeanRV64D

open LeanRV64D.Functions
open LeanRV64D.Defs

namespace EvmAsm.Rv64.SailEquiv

-- ============================================================================
-- Type abbreviations
-- ============================================================================

/-- The SAIL machine state type. -/
abbrev SailState := PreSail.SequentialState RegisterType trivialChoiceSource

/-- The SAIL monad. -/
abbrev SailM' := SailM

-- ============================================================================
-- Register mapping
-- ============================================================================

/-- Map Rv64.Reg to the SAIL 5-bit register index. -/
def regToRegidx : Reg → regidx
  | .x0  => Regidx 0
  | .x1  => Regidx 1
  | .x2  => Regidx 2
  | .x5  => Regidx 5
  | .x6  => Regidx 6
  | .x7  => Regidx 7
  | .x10 => Regidx 10
  | .x11 => Regidx 11
  | .x12 => Regidx 12

/-- All regToRegidx values are distinct. -/
theorem regToRegidx_injective : Function.Injective regToRegidx := by
  sorry

-- ============================================================================
-- Reading registers from SAIL state
-- ============================================================================

/-- Read an integer register from the SAIL state by running rX_bits. -/
noncomputable def sailGetReg (s : SailState) (idx : regidx) : Option (BitVec 64 × SailState) :=
  match rX_bits idx s with
  | .ok v s' => some (v, s')
  | .error _ _ => none

/-- Read the PC register from the SAIL state. -/
noncomputable def sailGetPC (s : SailState) : Option (BitVec 64) :=
  s.regs.get? Register.PC

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
-- State abstraction relation
-- ============================================================================

/-- The abstraction relation between Rv64.MachineState and SAIL state.

    Asserts that:
    1. Registers agree on the 9-register subset
    2. PC agrees
    3. Memory agrees (SAIL byte-addressed ↔ Rv64 doubleword-addressed)
    4. SAIL is in Machine mode with bare address translation (no MMU)
-/
structure StateRel (s_rv : MachineState) (s_sail : SailState) : Prop where
  /-- Registers agree: reading register r from Rv64 state equals reading it from SAIL state. -/
  reg_agree : ∀ (r : Reg),
    ∃ s_sail', sailGetReg s_sail (regToRegidx r) = some (s_rv.getReg r, s_sail')
  /-- PC values agree. -/
  pc_agree : sailGetPC s_sail = some s_rv.pc
  /-- Memory agrees: SAIL bytes reconstruct to Rv64 doublewords. -/
  mem_agree : ∀ (a : BitVec 64),
    reconstructDword s_sail.mem a.toNat = s_rv.getMem a
  /-- SAIL state is in Machine mode (bare address translation). -/
  bare_mode : True  -- TODO: refine to actual bare-mode predicate on s_sail

-- ============================================================================
-- StateRel preservation lemmas
-- ============================================================================

/-- Register write preserves StateRel for other registers and memory. -/
theorem StateRel.after_reg_write (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (r : Reg) (v : BitVec 64)
    (s_sail' : SailState)
    (h_write : ∀ r', r' ≠ r →
      sailGetReg s_sail' (regToRegidx r') = sailGetReg s_sail (regToRegidx r'))
    (h_written : sailGetReg s_sail' (regToRegidx r) = some (MachineState.getReg (s_rv.setReg r v) r, s_sail'))
    (h_pc : sailGetPC s_sail' = sailGetPC s_sail)
    (h_mem : s_sail'.mem = s_sail.mem) :
    StateRel (s_rv.setReg r v) s_sail' := by
  sorry

/-- PC update preserves StateRel for registers and memory. -/
theorem StateRel.after_pc_update (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (new_pc : BitVec 64)
    (s_sail' : SailState)
    (h_regs : ∀ r, sailGetReg s_sail' (regToRegidx r) = sailGetReg s_sail (regToRegidx r))
    (h_pc : sailGetPC s_sail' = some new_pc)
    (h_mem : s_sail'.mem = s_sail.mem) :
    StateRel (s_rv.setPC new_pc) s_sail' := by
  sorry

end EvmAsm.Rv64.SailEquiv
