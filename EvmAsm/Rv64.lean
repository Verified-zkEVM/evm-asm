/-
  EvmAsm.Rv64

  Root import file for the 64-bit RISC-V machine model (RV64IM).
-/

-- SyscallSpecs transitively imports Basic, Instructions, Program, SepLogic,
-- Execution, CPSSpec, GenericSpecs, InstructionSpecs, ByteOps, HalfwordOps,
-- WordOps, and Tactics.SpecDb. ControlFlow also covers Program directly.
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
-- RunBlock → SeqFrame → {XCancel → XPerm, PerfTrace, InstructionSpecs} + SpecDb.
-- LiftSpec → XSimp → XPerm.
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.LiftSpec
-- ExtractPure: design stub for #1432 (slice 1, beads evm-asm-bx7).
import EvmAsm.Rv64.Tactics.ExtractPure
-- XPermPartial: design stub for #156 (slice 1, beads evm-asm-a7k).
import EvmAsm.Rv64.Tactics.XPermPartial
import EvmAsm.Rv64.Tactics.XPermPure
-- DropPure: pure-stripping rebind tactic (#1435, beads evm-asm-ww8).
import EvmAsm.Rv64.Tactics.DropPure
import EvmAsm.Rv64.RLP
-- The `*Attr` files are imported by their non-Attr counterparts.
import EvmAsm.Rv64.RegOps
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.ByteAlg
-- SailEquiv leaves (each transitively imports ALUProofs → MonadLemmas → StateRel).
import EvmAsm.Rv64.SailEquiv.ShiftProofs
import EvmAsm.Rv64.SailEquiv.ImmProofs
import EvmAsm.Rv64.SailEquiv.BranchProofs
import EvmAsm.Rv64.SailEquiv.MemProofs
import EvmAsm.Rv64.SailEquiv.MExtProofs
