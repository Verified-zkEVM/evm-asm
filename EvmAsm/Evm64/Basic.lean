/-
  EvmAsm.Evm64.Basic

  Backward-compatibility wrapper: imports the pure `EvmWord.lean` (types
  and limb algebra) plus `Rv64.Basic` (the RV64 machine model). New pure
  consumers should import `EvmAsm.Evm64.EvmWord` directly to avoid
  dragging in Reg/Instr/MachineState.
-/

module

public import EvmAsm.Evm64.EvmWord
public import EvmAsm.Rv64.Basic

public section
