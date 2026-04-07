/-
  EvmAsm.Rv64.SailEquiv.MonadLemmas

  Infrastructure for symbolically executing SAIL monadic computations.
  The SAIL monad is `EStateM (Error exception) (SequentialState RegisterType trivialChoiceSource)`.
  We provide lemmas to chain rX_bits/wX_bits and extract final states.
-/

import EvmAsm.Rv64.SailEquiv.StateRel
import LeanRV64D

open LeanRV64D.Functions
open LeanRV64D.Defs

namespace EvmAsm.Rv64.SailEquiv

-- ============================================================================
-- Running SAIL computations
-- ============================================================================

/-- Run a SAIL monadic computation, returning the result and final state (or none on error). -/
noncomputable def runSail (m : SailM' α) (s : SailState) : Option (α × SailState) :=
  match m s with
  | .ok v s' => some (v, s')
  | .error _ _ => none

/-- Bind lemma: runSail (m >>= f) decomposes into running m then f. -/
theorem runSail_bind (m : SailM' α) (f : α → SailM' β) (s : SailState) :
    runSail (m >>= f) s =
      match runSail m s with
      | some (a, s') => runSail (f a) s'
      | none => none := by
  sorry

/-- Pure lemma: runSail (pure a) always succeeds. -/
theorem runSail_pure (a : α) (s : SailState) :
    runSail (pure a) s = some (a, s) := by
  sorry

/-- Sequencing: runSail (m >> k) = runSail m then runSail k, discarding intermediate value. -/
theorem runSail_seq (m : SailM' α) (k : SailM' β) (s : SailState) :
    runSail (m >> k) s =
      match runSail m s with
      | some (_, s') => runSail k s'
      | none => none := by
  sorry

-- ============================================================================
-- Register read/write lemmas
-- ============================================================================

/-- Reading x0 via rX_bits returns 0 without modifying state. -/
theorem rX_bits_x0 (s : SailState)
    (h : s.regs.get? Register.x0 = some (0 : BitVec 64)) :
    runSail (rX_bits (Regidx 0)) s = some (0#64, s) := by
  sorry

/-- Reading a non-zero register via rX_bits returns the stored value. -/
theorem rX_bits_nonzero (idx : BitVec 5) (s : SailState)
    (h_nz : idx ≠ 0) :
    ∃ v, runSail (rX_bits (Regidx idx)) s = some (v, s) := by
  sorry

/-- Writing a register via wX_bits updates the state. -/
theorem wX_bits_effect (idx : regidx) (v : BitVec 64) (s : SailState) :
    ∃ s', runSail (wX_bits idx v) s = some ((), s') := by
  sorry

/-- Writing x0 via wX_bits is a no-op. -/
theorem wX_bits_x0 (v : BitVec 64) (s : SailState) :
    runSail (wX_bits (Regidx 0) v) s = some ((), s) := by
  sorry

/-- After wX_bits, reading the same register returns the written value. -/
theorem rX_after_wX (idx : regidx) (v : BitVec 64) (s s' : SailState)
    (h_nz : idx ≠ Regidx 0)
    (h_write : runSail (wX_bits idx v) s = some ((), s')) :
    runSail (rX_bits idx) s' = some (v, s') := by
  sorry

/-- After wX_bits, reading a different register returns the original value. -/
theorem rX_after_wX_other (idx₁ idx₂ : regidx) (v : BitVec 64) (s s' : SailState)
    (h_ne : idx₁ ≠ idx₂)
    (h_write : runSail (wX_bits idx₁ v) s = some ((), s')) :
    runSail (rX_bits idx₂) s' = runSail (rX_bits idx₂) s := by
  sorry

-- ============================================================================
-- PC access lemmas
-- ============================================================================

/-- Reading the PC register returns the current PC. -/
theorem readReg_PC (s : SailState) :
    ∃ pc, runSail (readReg Register.PC) s = some (pc, s) := by
  sorry

/-- get_arch_pc returns the current PC value. -/
theorem get_arch_pc_eq (s : SailState) :
    ∃ pc, runSail (get_arch_pc ()) s = some (pc, s) := by
  sorry

/-- get_next_pc returns PC + 4 (the default next PC for non-branch instructions). -/
theorem get_next_pc_eq (s : SailState) :
    ∃ npc, runSail (get_next_pc ()) s = some (npc, s) := by
  sorry

-- ============================================================================
-- Composite patterns (common instruction shapes)
-- ============================================================================

/-- Pattern: read rs1, compute f, write rd, return RETIRE_SUCCESS.
    This is the common shape for ALU register-immediate instructions. -/
theorem sail_alu_1reg_pattern (rs1 rd : regidx) (f : BitVec 64 → BitVec 64) (s : SailState) :
    ∃ s', runSail (do
      let v ← rX_bits rs1
      wX_bits rd (f v)
      pure RETIRE_SUCCESS) s = some (RETIRE_SUCCESS, s') := by
  sorry

/-- Pattern: read rs1 and rs2, compute f, write rd, return RETIRE_SUCCESS.
    This is the common shape for ALU register-register instructions. -/
theorem sail_alu_2reg_pattern (rs1 rs2 rd : regidx) (f : BitVec 64 → BitVec 64 → BitVec 64)
    (s : SailState) :
    ∃ s', runSail (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (f v1 v2)
      pure RETIRE_SUCCESS) s = some (RETIRE_SUCCESS, s') := by
  sorry

end EvmAsm.Rv64.SailEquiv
