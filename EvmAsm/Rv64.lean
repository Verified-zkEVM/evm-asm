/-
  EvmAsm.Rv64

  Root import file for the 64-bit RISC-V machine model (RV64IM).
-/

-- SyscallSpecs transitively imports Basic, Instructions, Program, SepLogic,
-- Execution, CPSSpec, GenericSpecs, InstructionSpecs, ByteOps, HalfwordOps,
-- WordOps, and Tactics.SpecDb. ControlFlow also covers Program directly.
import EvmAsm.Rv64.Word
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.HintSpecs
import EvmAsm.Rv64.ControlFlow
-- WP: backward, soundness-first calculators over bounded CPS triples.
import EvmAsm.Rv64.WP.CFG
import EvmAsm.Rv64.WP.Call
import EvmAsm.Rv64.WP.Core
import EvmAsm.Rv64.WP.Examples
import EvmAsm.Rv64.WP.GeneratedCFG
import EvmAsm.Rv64.WP.Loop
import EvmAsm.Rv64.CPSCall
-- RunBlock → SeqFrame → {XCancel → XPerm, PerfTrace, InstructionSpecs} + SpecDb.
-- LiftSpec → XSimp → XPerm.
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.LiftSpec
import EvmAsm.Rv64.Tactics.WP
-- ExtractPure: design stub for #1432 (slice 1, beads evm-asm-bx7).
import EvmAsm.Rv64.Tactics.ExtractPure
-- XPermPartial: design stub for #156 (slice 1, beads evm-asm-a7k).
import EvmAsm.Rv64.Tactics.XPermPartial
import EvmAsm.Rv64.Tactics.XPermPure
-- XPermChunked: opt-in prototype for large sepConj chains (#265 slice 3).
import EvmAsm.Rv64.Tactics.XPermChunked
-- XPermCert: YOLO-style certificate permutation prover (default on).
import EvmAsm.Rv64.Tactics.XPermCert
-- DropPure: pure-stripping rebind tactic (#1435, beads evm-asm-ww8).
import EvmAsm.Rv64.Tactics.DropPure
-- XCancelStruct: structural cancellation tactic (#245 slice 3, beads evm-asm-otgf).
import EvmAsm.Rv64.Tactics.XCancelStruct
-- SymStep: symbolic-simulation prototype (#302 slice 2, beads evm-asm-avjm).
import EvmAsm.Rv64.Tactics.SymStep
import EvmAsm.Rv64.RLP
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionWrite
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.MemRegionWriteWide
-- The `*Attr` files are imported by their non-Attr counterparts.
import EvmAsm.Rv64.RegOps
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.ByteAlg
-- SailEquiv leaves (each transitively imports ALUProofs → MonadLemmas → StateRel).
import EvmAsm.Rv64.SailEquiv.InstrMap
import EvmAsm.Rv64.SailEquiv.ShiftProofs
import EvmAsm.Rv64.SailEquiv.ImmProofs
import EvmAsm.Rv64.SailEquiv.BranchProofs
import EvmAsm.Rv64.SailEquiv.MemProofs
-- VmemReduction: building blocks for discharging the MemProofs h_exec hypothesis.
import EvmAsm.Rv64.SailEquiv.VmemReduction
-- VmemReductionN: width-N generalisation discharging the sub-doubleword loads.
import EvmAsm.Rv64.SailEquiv.VmemReductionN
-- VmemReductionLoads: unconditional LW/LWU/LH/LHU/LB/LBU equivalence lemmas.
import EvmAsm.Rv64.SailEquiv.VmemReductionLoads
-- VmemWriteReduction: the store-side bare-mode write chain (writeBytes → vmem_write).
import EvmAsm.Rv64.SailEquiv.VmemWriteReduction
-- VmemReductionStores: unconditional SD/SW/SH/SB equivalence lemmas (Tier B).
import EvmAsm.Rv64.SailEquiv.VmemReductionStores
-- VmemConstruction: concrete bare-mode/PMA witnesses for memory side conditions.
import EvmAsm.Rv64.SailEquiv.VmemConstruction
-- StepSim consolidates the per-instruction lemmas into one step-simulation theorem.
import EvmAsm.Rv64.SailEquiv.StepSim
import EvmAsm.Rv64.SailEquiv.MExtProofs
import EvmAsm.Rv64.SailEquiv.StepProofs
import EvmAsm.Rv64.SailEquiv.MemReduce
import EvmAsm.Rv64.SailEquiv.MemMonad
-- SAsm: structured-assembly DSL (docs/sasm-design.md).
import EvmAsm.Rv64.SAsm
-- Image composition: footprint-satisfiability + CodeReq extent machinery
-- (bead 4ch8f.63).
import EvmAsm.Rv64.MemSat
import EvmAsm.Rv64.CodeReqExtents
