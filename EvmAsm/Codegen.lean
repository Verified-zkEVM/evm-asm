/-
  EvmAsm.Codegen

  Umbrella re-export for the codegen tool. See CODEGEN.md for the
  roadmap. Codegen was originally purely-additive (no proofs); since
  the Phase 1 codegen-proofs PR, it also carries kernel-checked
  invariants of the dispatcher registry (see `RegistryInvariants`).
-/

import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs
import EvmAsm.Codegen.RegionMap
import EvmAsm.Codegen.Driver
import EvmAsm.Codegen.Cli
import EvmAsm.Codegen.RoundTripTests
import EvmAsm.Codegen.Proofs
