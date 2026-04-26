/-
  EvmAsm.Rv64.RLP

  Root import file for the RISC-V RLP decoder (EL.3).

  Six-phase decoder bridging the pure RLP spec in `EvmAsm.EL.RLP` to
  RV64IM execution:
    Phase 1 — Prefix classifier  (5-way cascade on the first byte)
    Phase 2 — Length extraction  (planned)
    Phase 3 — Single-item decode (in progress: single-byte exit landed)
    Phase 4 — HINT_READ pipeline (planned)
    Phase 5 — Recursive list decode with explicit stack (planned)
    Phase 6 — Top-level pipeline (planned)
-/

-- Phase2LongLoopFive transitively covers Four → Three → Two → One →
-- Body → Iter. Phase2LongLoad covers Phase2LongAcc.
import EvmAsm.Rv64.RLP.Phase1
import EvmAsm.Rv64.RLP.Phase2Short
import EvmAsm.Rv64.RLP.Phase2LongLoad
import EvmAsm.Rv64.RLP.Phase2LongLoopFive
import EvmAsm.Rv64.RLP.Phase2LongLoopEight
import EvmAsm.Rv64.RLP.Phase2LongLoopSeven
import EvmAsm.Rv64.RLP.Phase2LongLoopSix
import EvmAsm.Rv64.RLP.Phase3LongString
import EvmAsm.Rv64.RLP.Phase3ShortString
import EvmAsm.Rv64.RLP.Phase3SingleByte
import EvmAsm.Rv64.RLP.Phase1CascadePrefixE2
import EvmAsm.Rv64.RLP.Phase1CascadePrefixE3
import EvmAsm.Rv64.RLP.Phase1E2FullPath
import EvmAsm.Rv64.RLP.Phase1StepToPhase3LongString
import EvmAsm.Rv64.RLP.Phase1ToPhase3SingleByte
import EvmAsm.Rv64.RLP.Phase1StepToPhase3ShortString
