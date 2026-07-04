/-
  EvmAsm.Codegen.Proofs

  Umbrella re-export for correctness theorems about the codegen
  layer. See CODEGEN.md's "Codegen-proofs" roadmap for the phase
  structure. Each phase lives in its own file under this directory.
-/

import EvmAsm.Codegen.Proofs.RegistryInvariants
import EvmAsm.Codegen.Proofs.CallReturn
import EvmAsm.Codegen.Proofs.HandlerSpecs
import EvmAsm.Codegen.Proofs.CreateInitcodeSizeValidSpec
import EvmAsm.Codegen.Proofs.CreateDeployedCodeValidSpec
import EvmAsm.Codegen.Proofs.U256IsZeroSpec
import EvmAsm.Codegen.Proofs.OpcodeTables
