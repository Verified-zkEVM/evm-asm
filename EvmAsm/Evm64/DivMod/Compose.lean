/-
  EvmAsm.Evm64.DivModCompose

  Hierarchical composition of DivMod CPS specs using CodeReq to avoid
  the WHNF scalability limit (25+ instruction atoms in a single theorem type).
  Each composed spec uses `divCode base` as a persistent CodeReq side-condition.

  Split into parallel sub-files for build performance:
  - Base: divCode/modCode definitions, skipBlock tactic, length lemmas
  - PhaseAB: Phase A/B compositions (zero path, cascade BNE, n=1..4)
  - CLZ: Count Leading Zeros (6-stage binary search)
  - Norm: PhaseC2, NormB, NormA, CopyAU, LoopSetup
  - Div128: div128 subroutine composition
  - Epilogue: Denorm, DIV/MOD epilogue
-/

import EvmAsm.Evm64.DivMod.Compose.PhaseAB
import EvmAsm.Evm64.DivMod.Compose.CLZ
import EvmAsm.Evm64.DivMod.Compose.Norm
import EvmAsm.Evm64.DivMod.Compose.NormA
import EvmAsm.Evm64.DivMod.Compose.Div128
import EvmAsm.Evm64.DivMod.Compose.Epilogue
import EvmAsm.Evm64.DivMod.Compose.ModPhaseB
import EvmAsm.Evm64.DivMod.Compose.ModPhaseBn3
import EvmAsm.Evm64.DivMod.Compose.ModPhaseBn21
import EvmAsm.Evm64.DivMod.Compose.ModCLZ
import EvmAsm.Evm64.DivMod.Compose.ModNorm
import EvmAsm.Evm64.DivMod.Compose.ModNormA
import EvmAsm.Evm64.DivMod.Compose.ModEpilogue
import EvmAsm.Evm64.DivMod.Compose.ModDiv128
import EvmAsm.Evm64.DivMod.Compose.FullPath
import EvmAsm.Evm64.DivMod.Compose.ModFullPath
