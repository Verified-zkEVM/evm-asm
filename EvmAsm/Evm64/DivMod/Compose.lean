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

-- FullPath transitively covers PhaseAB, CLZ, Norm, NormA, Epilogue, Base.
-- ModFullPath covers ModPhaseB, ModCLZ, ModNorm, ModNormA, ModEpilogue, Epilogue.
-- ModFullPathN3 covers ModPhaseBn3 (plus ModFullPath's chain).
-- ModFullPathN{2,1} cover ModPhaseBn21.
-- ModDiv128 covers Div128.
import EvmAsm.Evm64.DivMod.Compose.ModDiv128
import EvmAsm.Evm64.DivMod.Compose.FullPath
import EvmAsm.Evm64.DivMod.Compose.FullPathN3
import EvmAsm.Evm64.DivMod.Compose.FullPathN2
import EvmAsm.Evm64.DivMod.Compose.FullPathN1
import EvmAsm.Evm64.DivMod.Compose.ModFullPath
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN3
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN2
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN1
