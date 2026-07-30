import EvmAsm.Codegen.CallFramePhase
import EvmAsm.Codegen.CallFrameWindows
import EvmAsm.Codegen.Cli
import EvmAsm.Codegen.Driver
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.FileSizeGuard
import EvmAsm.Codegen.Programs.Registry
-- BOOTSTRAP import EvmAsm.Codegen.Proofs.BlobHashGuardedHandlerSpec
-- BOOTSTRAP import EvmAsm.Codegen.Proofs.BlockHashGuardedHandlerSpec
-- BOOTSTRAP import EvmAsm.Codegen.Proofs.CallReturn
-- BOOTSTRAP import EvmAsm.Codegen.Proofs.CalldataLoadGuardedHandlerSpec
-- BOOTSTRAP import EvmAsm.Codegen.Proofs.CreateDeployedCodeValidSpec
-- BOOTSTRAP import EvmAsm.Codegen.Proofs.CreateInitcodeSizeValidSpec
-- BOOTSTRAP import EvmAsm.Codegen.Proofs.DoWhileDemo
-- BOOTSTRAP import EvmAsm.Codegen.Proofs.GuardedHandlerSpecs
-- BOOTSTRAP import EvmAsm.Codegen.Proofs.GuestImage
-- BOOTSTRAP import EvmAsm.Codegen.Proofs.GuestImageEntries
-- BOOTSTRAP import EvmAsm.Codegen.Proofs.HandleFocusReal
-- BOOTSTRAP import EvmAsm.Codegen.Proofs.HandlerHandles
-- BOOTSTRAP import EvmAsm.Codegen.Proofs.HandlerHandlesBinary
-- BOOTSTRAP import EvmAsm.Codegen.Proofs.HandlerHandlesLogic
-- BOOTSTRAP import EvmAsm.Codegen.Proofs.HandlerHandlesUnary
-- BOOTSTRAP import EvmAsm.Codegen.Proofs.HandlerSpecs
-- BOOTSTRAP import EvmAsm.Codegen.Proofs.OpcodeTables
-- BOOTSTRAP import EvmAsm.Codegen.Proofs.RegistryInvariants
-- BOOTSTRAP import EvmAsm.Codegen.Proofs.U256IsZeroSpec
import EvmAsm.Codegen.RegionMap
import EvmAsm.Codegen.RoundTripTests

def main (args : List String) : IO UInt32 :=
  EvmAsm.Codegen.Cli.main args
