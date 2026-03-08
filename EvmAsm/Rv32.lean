/-
  EvmAsm.Rv32

  Root import file for the 32-bit RISC-V machine model (RV32IM).
-/

import EvmAsm.Rv32.Basic
import EvmAsm.Rv32.Instructions
import EvmAsm.Rv32.Program
import EvmAsm.Rv32.SepLogic
import EvmAsm.Rv32.MulMacro
import EvmAsm.Rv32.Execution
import EvmAsm.Rv32.CPSSpec
import EvmAsm.Rv32.GenericSpecs
import EvmAsm.Rv32.InstructionSpecs
import EvmAsm.Rv32.ControlFlow
import EvmAsm.Rv32.SyscallSpecs
import EvmAsm.Rv32.Tactics.XPerm
import EvmAsm.Rv32.Tactics.XSimp
import EvmAsm.Rv32.Tactics.XCancel
import EvmAsm.Rv32.Tactics.SeqFrame
import EvmAsm.Rv32.Tactics.SpecDb
import EvmAsm.Rv32.Tactics.RunBlock
import EvmAsm.Rv32.Tactics.LiftSpec
