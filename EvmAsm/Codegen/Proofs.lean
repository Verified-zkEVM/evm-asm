/-
  EvmAsm.Codegen.Proofs

  Umbrella re-export for correctness theorems about the codegen
  layer. See CODEGEN.md's "Codegen-proofs" roadmap for the phase
  structure. Each phase lives in its own file under this directory.
-/

import EvmAsm.Codegen.Proofs.RegistryInvariants
import EvmAsm.Codegen.Proofs.CallReturn
import EvmAsm.Codegen.Proofs.HandlerSpecs
import EvmAsm.Codegen.Proofs.GuardedHandlerSpecs
import EvmAsm.Codegen.Proofs.CalldataLoadGuardedHandlerSpec
import EvmAsm.Codegen.Proofs.BlobHashGuardedHandlerSpec
import EvmAsm.Codegen.Proofs.BlockHashGuardedHandlerSpec
import EvmAsm.Codegen.Proofs.HandlerHandles
import EvmAsm.Codegen.Proofs.HandlerHandlesBinary
import EvmAsm.Codegen.Proofs.HandlerHandlesLogic
import EvmAsm.Codegen.Proofs.HandlerHandlesUnary
import EvmAsm.Codegen.Proofs.HandleFocusReal
import EvmAsm.Codegen.Proofs.CreateInitcodeSizeValidSpec
import EvmAsm.Codegen.Proofs.CreateDeployedCodeValidSpec
import EvmAsm.Codegen.Proofs.U256IsZeroSpec
import EvmAsm.Codegen.Proofs.JumpdestBitmap
import EvmAsm.Codegen.Proofs.OpcodeTables
import EvmAsm.Codegen.Proofs.GuestImageEntries
import EvmAsm.Codegen.Proofs.GuestImage
import EvmAsm.Codegen.Proofs.DoWhileDemo
