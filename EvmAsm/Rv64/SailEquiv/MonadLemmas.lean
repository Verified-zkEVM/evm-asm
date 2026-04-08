/-
  EvmAsm.Rv64.SailEquiv.MonadLemmas

  Infrastructure for symbolically executing SAIL monadic computations.
  The SAIL monad is `EStateM (Error exception) (SequentialState RegisterType trivialChoiceSource)`.
-/

import EvmAsm.Rv64.SailEquiv.StateRel
import LeanRV64D

open LeanRV64D.Functions
open Sail

namespace EvmAsm.Rv64.SailEquiv

-- ============================================================================
-- EStateM basics
-- ============================================================================

@[simp]
theorem runSail_pure (a : α) (s : SailState) :
    runSail (pure a : SailM α) s = some (a, s) := by
  simp [runSail, pure, EStateM.pure]

@[simp]
theorem runSail_bind (m : SailM α) (f : α → SailM β) (s : SailState) :
    runSail (m >>= f) s =
      match runSail m s with
      | some (a, s') => runSail (f a) s'
      | none => none := by
  simp only [runSail, bind, EStateM.bind]
  cases h : m s with
  | ok v s' => simp
  | error e s' => simp

-- ============================================================================
-- BitVec.toNat reduction for register indices
-- ============================================================================

private theorem bv5_toNat_1 : BitVec.toNat (1 : BitVec 5) = 1 := by decide
private theorem bv5_toNat_2 : BitVec.toNat (2 : BitVec 5) = 2 := by decide
private theorem bv5_toNat_5 : BitVec.toNat (5 : BitVec 5) = 5 := by decide
private theorem bv5_toNat_6 : BitVec.toNat (6 : BitVec 5) = 6 := by decide
private theorem bv5_toNat_7 : BitVec.toNat (7 : BitVec 5) = 7 := by decide
private theorem bv5_toNat_10 : BitVec.toNat (10 : BitVec 5) = 10 := by decide
private theorem bv5_toNat_11 : BitVec.toNat (11 : BitVec 5) = 11 := by decide
private theorem bv5_toNat_12 : BitVec.toNat (12 : BitVec 5) = 12 := by decide

-- Common simp arguments for rX_bits proofs
-- We unfold: runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg
-- We reduce: Int.toNat, bv5_toNat_N (to get concrete Nat for match)
-- We unfold: PreSail.readReg, EStateM.get (to expose the Option match on regs.get?)
-- We use: h (the hypothesis that the register is present)

-- ============================================================================
-- rX_bits — per-register read lemmas
-- ============================================================================

theorem runSail_rX_bits_x0 (s : SailState) :
    runSail (rX_bits (regidx.Regidx 0)) s = some (0#64, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, zero_reg, zeros, regval_from_reg,
    pure, EStateM.pure, bind, EStateM.bind]

theorem runSail_rX_bits_x1 (s : SailState) (v : BitVec 64)
    (h : s.regs.get? Register.x1 = some v) :
    runSail (rX_bits (regidx.Regidx 1)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get, EStateM.modifyGet]

theorem runSail_rX_bits_x2 (s : SailState) (v : BitVec 64)
    (h : s.regs.get? Register.x2 = some v) :
    runSail (rX_bits (regidx.Regidx 2)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

theorem runSail_rX_bits_x5 (s : SailState) (v : BitVec 64)
    (h : s.regs.get? Register.x5 = some v) :
    runSail (rX_bits (regidx.Regidx 5)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

theorem runSail_rX_bits_x6 (s : SailState) (v : BitVec 64)
    (h : s.regs.get? Register.x6 = some v) :
    runSail (rX_bits (regidx.Regidx 6)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

theorem runSail_rX_bits_x7 (s : SailState) (v : BitVec 64)
    (h : s.regs.get? Register.x7 = some v) :
    runSail (rX_bits (regidx.Regidx 7)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

theorem runSail_rX_bits_x10 (s : SailState) (v : BitVec 64)
    (h : s.regs.get? Register.x10 = some v) :
    runSail (rX_bits (regidx.Regidx 10)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

theorem runSail_rX_bits_x11 (s : SailState) (v : BitVec 64)
    (h : s.regs.get? Register.x11 = some v) :
    runSail (rX_bits (regidx.Regidx 11)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

theorem runSail_rX_bits_x12 (s : SailState) (v : BitVec 64)
    (h : s.regs.get? Register.x12 = some v) :
    runSail (rX_bits (regidx.Regidx 12)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

-- ============================================================================
-- Bridge lemma: rX_bits from StateRel
-- ============================================================================

/-- If StateRel holds, reading any Rv64 register from the SAIL state via rX_bits
    returns the same value as getReg, without modifying state. -/
theorem runSail_rX_bits_of_stateRel (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (r : Reg) :
    runSail (rX_bits (regToRegidx r)) s_sail = some (s_rv.getReg r, s_sail) := by
  have ha := hrel.reg_agree r
  cases r <;> simp [regToRegidx, sailRegVal, MachineState.getReg] at ha ⊢ <;>
  · first
      | exact runSail_rX_bits_x0 s_sail
      | exact runSail_rX_bits_x1 s_sail _ ha
      | exact runSail_rX_bits_x2 s_sail _ ha
      | exact runSail_rX_bits_x5 s_sail _ ha
      | exact runSail_rX_bits_x6 s_sail _ ha
      | exact runSail_rX_bits_x7 s_sail _ ha
      | exact runSail_rX_bits_x10 s_sail _ ha
      | exact runSail_rX_bits_x11 s_sail _ ha
      | exact runSail_rX_bits_x12 s_sail _ ha

-- ============================================================================
-- wX_bits — register write
-- ============================================================================

theorem runSail_wX_bits_x0 (v : BitVec 64) (s : SailState) :
    runSail (wX_bits (regidx.Regidx 0) v) s = some (⟨⟩, s) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt,
    pure, EStateM.pure, bind, EStateM.bind]

/-- wX_bits on a non-x0 register: writes the value and calls the (no-op) callback.
    The final state has the register updated and everything else unchanged. -/
theorem runSail_wX_bits_x1 (v : BitVec 64) (s : SailState) :
    runSail (wX_bits (regidx.Regidx 1) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x1 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure,
    get, MonadState.get, getThe, MonadStateOf.get]

theorem runSail_wX_bits_x2 (v : BitVec 64) (s : SailState) :
    runSail (wX_bits (regidx.Regidx 2) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x2 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure,
    get, MonadState.get, getThe, MonadStateOf.get]

theorem runSail_wX_bits_x5 (v : BitVec 64) (s : SailState) :
    runSail (wX_bits (regidx.Regidx 5) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x5 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure,
    get, MonadState.get, getThe, MonadStateOf.get]

theorem runSail_wX_bits_x6 (v : BitVec 64) (s : SailState) :
    runSail (wX_bits (regidx.Regidx 6) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x6 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure,
    get, MonadState.get, getThe, MonadStateOf.get]

theorem runSail_wX_bits_x7 (v : BitVec 64) (s : SailState) :
    runSail (wX_bits (regidx.Regidx 7) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x7 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure,
    get, MonadState.get, getThe, MonadStateOf.get]

theorem runSail_wX_bits_x10 (v : BitVec 64) (s : SailState) :
    runSail (wX_bits (regidx.Regidx 10) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x10 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure,
    get, MonadState.get, getThe, MonadStateOf.get]

theorem runSail_wX_bits_x11 (v : BitVec 64) (s : SailState) :
    runSail (wX_bits (regidx.Regidx 11) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x11 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure,
    get, MonadState.get, getThe, MonadStateOf.get]

theorem runSail_wX_bits_x12 (v : BitVec 64) (s : SailState) :
    runSail (wX_bits (regidx.Regidx 12) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x12 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure,
    get, MonadState.get, getThe, MonadStateOf.get]

-- ============================================================================
-- xreg_write_callback — no-op on state
-- ============================================================================

theorem runSail_xreg_write_callback (reg : regidx) (v : BitVec 64) (s : SailState) :
    runSail (xreg_write_callback reg v) s = some (⟨⟩, s) := by
  simp [runSail, xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not,
    bind, EStateM.bind, pure, EStateM.pure]

-- ============================================================================
-- PC access
-- ============================================================================

/-- get_arch_pc reads the PC register without modifying state. -/
theorem runSail_get_arch_pc (s : SailState) (pc : BitVec 64)
    (h : s.regs.get? Register.PC = some pc) :
    runSail (get_arch_pc ()) s = some (pc, s) := by
  simp [runSail, get_arch_pc, PreSail.readReg, h,
    pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

end EvmAsm.Rv64.SailEquiv
