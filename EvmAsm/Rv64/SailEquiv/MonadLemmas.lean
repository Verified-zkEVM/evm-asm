/-
  EvmAsm.Rv64.SailEquiv.MonadLemmas

  Infrastructure for symbolically executing SAIL monadic computations.
  The SAIL monad is `EStateM (Error exception) (SequentialState RegisterType trivialChoiceSource)`.
-/

import EvmAsm.Rv64.SailEquiv.StateRel

open LeanRV64D.Functions
open Sail

namespace EvmAsm.Rv64.SailEquiv

-- ============================================================================
-- EStateM basics
-- ============================================================================

@[simp]
theorem runSail_pure {a : α} {s : SailState} :
    runSail (pure a : SailM α) s = some (a, s) := by
  simp [runSail, pure, EStateM.pure]

@[simp]
theorem runSail_bind {m : SailM α} {f : α → SailM β} {s : SailState} :
    runSail (m >>= f) s =
      match runSail m s with
      | some (a, s') => runSail (f a) s'
      | none => none := by
  simp only [runSail, bind, EStateM.bind]
  cases h : m s with
  | ok v s' => simp
  | error e s' => simp

-- ============================================================================
-- rX_bits — per-register read lemmas
--
-- Common simp arguments: runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
-- PreSail.readReg, EStateM.get, plus the hypothesis `h` witnessing the register
-- has a value. The `Int.toNat` and `BitVec.toNat`-on-numeric-literal reductions
-- fire via `decide` inside simp; we no longer maintain a per-index table.
-- ============================================================================

theorem runSail_rX_bits_x0 {s : SailState} :
    runSail (rX_bits (regidx.Regidx 0)) s = some (0#64, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, zero_reg, zeros, regval_from_reg,
    pure, EStateM.pure, bind, EStateM.bind]

private theorem runSail_rX_bits_x1 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x1 = some v) :
    runSail (rX_bits (regidx.Regidx 1)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x2 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x2 = some v) :
    runSail (rX_bits (regidx.Regidx 2)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x3 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x3 = some v) :
    runSail (rX_bits (regidx.Regidx 3)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x4 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x4 = some v) :
    runSail (rX_bits (regidx.Regidx 4)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x5 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x5 = some v) :
    runSail (rX_bits (regidx.Regidx 5)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x6 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x6 = some v) :
    runSail (rX_bits (regidx.Regidx 6)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x7 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x7 = some v) :
    runSail (rX_bits (regidx.Regidx 7)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x8 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x8 = some v) :
    runSail (rX_bits (regidx.Regidx 8)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x9 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x9 = some v) :
    runSail (rX_bits (regidx.Regidx 9)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x10 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x10 = some v) :
    runSail (rX_bits (regidx.Regidx 10)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x11 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x11 = some v) :
    runSail (rX_bits (regidx.Regidx 11)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x12 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x12 = some v) :
    runSail (rX_bits (regidx.Regidx 12)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x13 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x13 = some v) :
    runSail (rX_bits (regidx.Regidx 13)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x14 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x14 = some v) :
    runSail (rX_bits (regidx.Regidx 14)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x15 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x15 = some v) :
    runSail (rX_bits (regidx.Regidx 15)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x16 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x16 = some v) :
    runSail (rX_bits (regidx.Regidx 16)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x17 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x17 = some v) :
    runSail (rX_bits (regidx.Regidx 17)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x18 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x18 = some v) :
    runSail (rX_bits (regidx.Regidx 18)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x19 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x19 = some v) :
    runSail (rX_bits (regidx.Regidx 19)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x20 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x20 = some v) :
    runSail (rX_bits (regidx.Regidx 20)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x21 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x21 = some v) :
    runSail (rX_bits (regidx.Regidx 21)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x22 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x22 = some v) :
    runSail (rX_bits (regidx.Regidx 22)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x23 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x23 = some v) :
    runSail (rX_bits (regidx.Regidx 23)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x24 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x24 = some v) :
    runSail (rX_bits (regidx.Regidx 24)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x25 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x25 = some v) :
    runSail (rX_bits (regidx.Regidx 25)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x26 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x26 = some v) :
    runSail (rX_bits (regidx.Regidx 26)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x27 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x27 = some v) :
    runSail (rX_bits (regidx.Regidx 27)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x28 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x28 = some v) :
    runSail (rX_bits (regidx.Regidx 28)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x29 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x29 = some v) :
    runSail (rX_bits (regidx.Regidx 29)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x30 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x30 = some v) :
    runSail (rX_bits (regidx.Regidx 30)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

private theorem runSail_rX_bits_x31 {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.x31 = some v) :
    runSail (rX_bits (regidx.Regidx 31)) s = some (v, s) := by
  simp [runSail, rX_bits, rX, BitVec.toNatInt, regval_from_reg,
    PreSail.readReg, h, pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

-- ============================================================================
-- Bridge lemma: rX_bits from StateRel
-- ============================================================================

/-- If StateRel holds, reading any Rv64 register from the SAIL state via rX_bits
    returns the same value as getReg, without modifying state. -/
theorem runSail_rX_bits_of_stateRel {sRv : MachineState} {sSail : SailState}
    (hrel : StateRel sRv sSail) (r : Reg) :
    runSail (rX_bits (regToRegidx r)) sSail = some (sRv.getReg r, sSail) := by
  have ha := hrel.reg_agree r
  cases r <;> simp [regToRegidx, sailRegVal, MachineState.getReg] at ha ⊢
  case x0 => exact runSail_rX_bits_x0
  case x1 => exact runSail_rX_bits_x1 ha
  case x2 => exact runSail_rX_bits_x2 ha
  case x3 => exact runSail_rX_bits_x3 ha
  case x4 => exact runSail_rX_bits_x4 ha
  case x5 => exact runSail_rX_bits_x5 ha
  case x6 => exact runSail_rX_bits_x6 ha
  case x7 => exact runSail_rX_bits_x7 ha
  case x8 => exact runSail_rX_bits_x8 ha
  case x9 => exact runSail_rX_bits_x9 ha
  case x10 => exact runSail_rX_bits_x10 ha
  case x11 => exact runSail_rX_bits_x11 ha
  case x12 => exact runSail_rX_bits_x12 ha
  case x13 => exact runSail_rX_bits_x13 ha
  case x14 => exact runSail_rX_bits_x14 ha
  case x15 => exact runSail_rX_bits_x15 ha
  case x16 => exact runSail_rX_bits_x16 ha
  case x17 => exact runSail_rX_bits_x17 ha
  case x18 => exact runSail_rX_bits_x18 ha
  case x19 => exact runSail_rX_bits_x19 ha
  case x20 => exact runSail_rX_bits_x20 ha
  case x21 => exact runSail_rX_bits_x21 ha
  case x22 => exact runSail_rX_bits_x22 ha
  case x23 => exact runSail_rX_bits_x23 ha
  case x24 => exact runSail_rX_bits_x24 ha
  case x25 => exact runSail_rX_bits_x25 ha
  case x26 => exact runSail_rX_bits_x26 ha
  case x27 => exact runSail_rX_bits_x27 ha
  case x28 => exact runSail_rX_bits_x28 ha
  case x29 => exact runSail_rX_bits_x29 ha
  case x30 => exact runSail_rX_bits_x30 ha
  case x31 => exact runSail_rX_bits_x31 ha

-- ============================================================================
-- wX_bits — register write
-- ============================================================================

theorem runSail_wX_bits_x0 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 0) v) s = some (⟨⟩, s) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt,
    pure, EStateM.pure, bind, EStateM.bind]

/-- wX_bits on a non-x0 register: writes the value and calls the (no-op) callback.
    The final state has the register updated and everything else unchanged. -/
private theorem runSail_wX_bits_x1 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 1) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x1 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x2 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 2) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x2 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x3 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 3) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x3 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x4 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 4) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x4 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x5 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 5) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x5 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x6 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 6) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x6 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x7 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 7) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x7 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x8 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 8) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x8 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x9 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 9) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x9 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x10 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 10) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x10 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x11 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 11) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x11 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x12 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 12) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x12 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x13 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 13) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x13 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x14 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 14) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x14 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x15 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 15) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x15 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x16 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 16) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x16 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x17 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 17) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x17 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x18 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 18) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x18 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x19 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 19) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x19 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x20 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 20) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x20 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x21 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 21) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x21 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x22 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 22) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x22 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x23 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 23) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x23 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x24 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 24) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x24 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x25 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 25) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x25 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x26 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 26) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x26 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x27 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 27) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x27 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x28 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 28) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x28 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x29 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 29) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x29 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x30 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 30) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x30 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

private theorem runSail_wX_bits_x31 {v : BitVec 64} {s : SailState} :
    runSail (wX_bits (regidx.Regidx 31) v) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.x31 v }) := by
  simp [runSail, wX_bits, wX, BitVec.toNatInt, regval_into_reg,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not, to_bits, get_slice_int,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Generic `wX_bits` dispatch: for any `rd : Reg`, the SAIL write reduces
    uniformly to `sailStateWithReg sSail rd v`. Collapses the per-register
    `cases rd <;> simp …` dispatch in downstream instruction proofs. -/
theorem runSail_wX_bits_of_reg (sSail : SailState) (rd : Reg) (v : BitVec 64) :
    runSail (wX_bits (regToRegidx rd) v) sSail =
      some (⟨⟩, sailStateWithReg sSail rd v) := by
  cases rd <;>
    simp only [regToRegidx, sailStateWithReg,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x3, runSail_wX_bits_x4, runSail_wX_bits_x5,
      runSail_wX_bits_x6, runSail_wX_bits_x7, runSail_wX_bits_x8,
      runSail_wX_bits_x9, runSail_wX_bits_x10, runSail_wX_bits_x11,
      runSail_wX_bits_x12, runSail_wX_bits_x13, runSail_wX_bits_x14,
      runSail_wX_bits_x15, runSail_wX_bits_x16, runSail_wX_bits_x17,
      runSail_wX_bits_x18, runSail_wX_bits_x19, runSail_wX_bits_x20,
      runSail_wX_bits_x21, runSail_wX_bits_x22, runSail_wX_bits_x23,
      runSail_wX_bits_x24, runSail_wX_bits_x25, runSail_wX_bits_x26,
      runSail_wX_bits_x27, runSail_wX_bits_x28, runSail_wX_bits_x29,
      runSail_wX_bits_x30, runSail_wX_bits_x31]

-- ============================================================================
-- xreg_write_callback — no-op on state
-- ============================================================================

theorem runSail_xreg_write_callback {reg : regidx} {v : BitVec 64} {s : SailState} :
    runSail (xreg_write_callback reg v) s = some (⟨⟩, s) := by
  simp [runSail, xreg_write_callback, reg_name_forwards,
    get_config_use_abi_names, encdec_reg_forwards_matches, encdec_reg_forwards,
    xreg_full_write_callback, LeanRV64D.Functions.not,
    bind, EStateM.bind, pure, EStateM.pure]

-- ============================================================================
-- PC access
-- ============================================================================

/-- get_arch_pc reads the PC register without modifying state. -/
theorem runSail_get_arch_pc {s : SailState} {pc : BitVec 64}
    (h : s.regs.get? Register.PC = some pc) :
    runSail (get_arch_pc ()) s = some (pc, s) := by
  simp [runSail, get_arch_pc, PreSail.readReg, h,
    pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

-- ============================================================================
-- Branch/jump infrastructure
-- ============================================================================

/-- readReg PC returns the PC value without modifying state. -/
theorem runSail_readReg_PC {s : SailState} {pc : BitVec 64}
    (h : s.regs.get? Register.PC = some pc) :
    runSail (readReg Register.PC : SailM (BitVec 64)) s = some (pc, s) := by
  simp [runSail, PreSail.readReg, h,
    pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

/-- set_next_pc writes the nextPC register (+ two no-op callbacks). -/
theorem runSail_set_next_pc {target : BitVec 64} {s : SailState} :
    runSail (set_next_pc target) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.nextPC target }) := by
  simp [runSail, set_next_pc,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    bind, EStateM.bind, pure, EStateM.pure]

/-- get_next_pc reads the nextPC register. -/
theorem runSail_get_next_pc {s : SailState} {v : BitVec 64}
    (h : s.regs.get? Register.nextPC = some v) :
    runSail (get_next_pc ()) s = some (v, s) := by
  simp [runSail, get_next_pc, PreSail.readReg, h,
    pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

-- ============================================================================
-- jump_to (for branches and jumps)
-- ============================================================================

@[simp] private theorem sail_access_eq (v : BitVec w) (i : Nat) :
    Sail.BitVec.access v i = BitVec.ofBool v[i]! := rfl

private theorem align4_bit0 (v : BitVec 64) (h : v &&& 3 = 0) :
    v[0] = false := by
  show v.getLsbD 0 = false
  have := congrArg (·.getLsbD 0) h; simp at this; exact this

private theorem align4_bit1 (v : BitVec 64) (h : v &&& 3 = 0) :
    v[1] = false := by
  show v.getLsbD 1 = false
  have := congrArg (·.getLsbD 1) h; simp at this; exact this

/-- currentlyEnabled Ext_Zca succeeds when misa is readable.
    Returns the MISA C-bit check result without modifying state. -/
-- currentlyEnabled Ext_Zca → Ext_C → readReg misa. Both hartSupports are true.
private theorem currentlyEnabled_Ext_C_result (s : SailState) (misa_val : BitVec 64)
    (h_misa : s.regs.get? Register.misa = some misa_val) :
    currentlyEnabled extension.Ext_C s =
      EStateM.Result.ok ((_get_Misa_C misa_val) == 1#1) s := by
  rw [currentlyEnabled.eq_def]
  simp [hartSupports, _get_Misa_C, LeanRV64D.Functions.not, LeanRV64D.Functions.xlen,
    PreSail.readReg, h_misa,
    pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

theorem currentlyEnabled_Ext_Zca_result (s : SailState) (misa_val : BitVec 64)
    (h_misa : s.regs.get? Register.misa = some misa_val) :
    currentlyEnabled extension.Ext_Zca s =
      EStateM.Result.ok ((_get_Misa_C misa_val) == 1#1) s := by
  rw [currentlyEnabled.eq_def]
  simp [hartSupports, LeanRV64D.Functions.not, LeanRV64D.Functions.xlen,
    currentlyEnabled_Ext_C_result s misa_val h_misa,
    pure, EStateM.pure, bind, EStateM.bind]

private theorem align4_getLsbD0 (v : BitVec 64) (h : v &&& 3 = 0) :
    v.getLsbD 0 = false := by
  have := congrArg (·.getLsbD 0) h; simp at this; exact this

private theorem align4_getLsbD1 (v : BitVec 64) (h : v &&& 3 = 0) :
    v.getLsbD 1 = false := by
  have := congrArg (·.getLsbD 1) h; simp at this; exact this

/-- jump_to succeeds for 4-byte aligned targets: writes nextPC, returns RETIRE_SUCCESS.
    Requires 4-byte alignment (bits 0,1 = 0) and that misa is readable in the
    SAIL state. Alignment makes the Ext_Zca result irrelevant (bit 1 = 0). -/
theorem runSail_jump_to {target : BitVec 64} {s : SailState}
    (misa_val : BitVec 64)
    (h_align : target &&& 3 = 0)
    (h_misa : s.regs.get? Register.misa = some misa_val) :
    runSail (jump_to target) s =
      some (RETIRE_SUCCESS, { s with regs := s.regs.insert Register.nextPC target }) := by
  have hb0 : target.getLsbD 0 = false := align4_getLsbD0 target h_align
  have hb1 : target.getLsbD 1 = false := align4_getLsbD1 target h_align
  -- target[0] and target[1] are definitionally target.getLsbD 0/1
  have hb0' : target[0] = false := hb0
  have hb1' : target[1] = false := hb1
  have h_zca := currentlyEnabled_Ext_Zca_result s misa_val h_misa
  unfold jump_to runSail
  simp [SailME.run, PreSail.PreSailME.run,
    ext_control_check_pc,
    assert, PreSail.assert,
    hb0', hb1', BitVec.ofBool,
    bit_to_bool, bool_bit_backwards,
    h_zca, LeanRV64D.Functions.not,
    set_next_pc, redirect_callback,
    PreSail.writeReg, EStateM.modifyGet,
    modify, MonadState.modifyGet, modifyGet, MonadStateOf.modifyGet,
    pure, EStateM.pure, bind, EStateM.bind,
    MonadLift.monadLift, monadLift, liftM, Functor.map,
    ExceptT.run, ExceptT.mk, ExceptT.pure,
    ExceptT.bind, ExceptT.bindCont, ExceptT.lift,
    EStateM.map, RETIRE_SUCCESS]

end EvmAsm.Rv64.SailEquiv
