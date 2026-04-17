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

-- ============================================================================
-- Branch/jump infrastructure
-- ============================================================================

/-- readReg PC returns the PC value without modifying state. -/
theorem runSail_readReg_PC (s : SailState) (pc : BitVec 64)
    (h : s.regs.get? Register.PC = some pc) :
    runSail (readReg Register.PC : SailM (BitVec 64)) s = some (pc, s) := by
  simp [runSail, PreSail.readReg, h,
    pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get]

/-- set_next_pc writes the nextPC register (+ two no-op callbacks). -/
theorem runSail_set_next_pc (target : BitVec 64) (s : SailState) :
    runSail (set_next_pc target) s =
      some (⟨⟩, { s with regs := s.regs.insert Register.nextPC target }) := by
  simp [runSail, set_next_pc, sail_branch_announce, redirect_callback,
    PreSail.writeReg, EStateM.modifyGet, modify, MonadState.modifyGet,
    modifyGet, MonadStateOf.modifyGet,
    bind, EStateM.bind, pure, EStateM.pure,
    get, MonadState.get, getThe, MonadStateOf.get,
    LeanRV64D.Functions.xlen]

/-- get_next_pc reads the nextPC register. -/
theorem runSail_get_next_pc (s : SailState) (v : BitVec 64)
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
theorem runSail_jump_to (target : BitVec 64) (s : SailState)
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
    set_next_pc, sail_branch_announce, redirect_callback,
    PreSail.writeReg, EStateM.modifyGet,
    modify, MonadState.modifyGet, modifyGet, MonadStateOf.modifyGet,
    pure, EStateM.pure, bind, EStateM.bind, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get,
    MonadLift.monadLift, monadLift, liftM, Functor.map, Function.comp,
    ExceptT.run, ExceptT.mk, ExceptT.pure,
    ExceptT.bind, ExceptT.bindCont, ExceptT.lift,
    ExceptT.instMonadLift, EStateM.map,
    LeanRV64D.Functions.xlen, RETIRE_SUCCESS]

end EvmAsm.Rv64.SailEquiv
