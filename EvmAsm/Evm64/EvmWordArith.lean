/-
  EvmAsm.Evm64.EvmWordArith

  Mathematical correctness lemmas connecting limb-level computations
  to 256-bit EvmWord operations. Used by stack-level specs.

  Re-exports all sub-modules for backwards compatibility. Many of the
  listed leaves transitively cover their Arithmetic / MultiLimb /
  Common prefix chain; see per-module comments below for the routing.
-/

-- Opcode-specific leaves that nothing else here imports:
import EvmAsm.Evm64.EvmWordArith.IsZero
import EvmAsm.Evm64.EvmWordArith.Eq
import EvmAsm.Evm64.EvmWordArith.Comparison
import EvmAsm.Evm64.EvmWordArith.ByteOps
import EvmAsm.Evm64.EvmWordArith.SignExtend

-- MulCorrect covers Arithmetic → MultiLimb → Common.
import EvmAsm.Evm64.EvmWordArith.MulCorrect

-- DivAccumulate covers DivRemainderBound → DivAddbackLimb →
-- DivMulSubLimb → DivLimbBridge → DivBridge → Normalization →
-- MulSubChain → Div128Lemmas → MultiLimb → Div → Common.
import EvmAsm.Evm64.EvmWordArith.DivAccumulate

-- Carry extensions of the Limb variants.
import EvmAsm.Evm64.EvmWordArith.DivMulSubCarry
import EvmAsm.Evm64.EvmWordArith.DivAddbackCarry

-- Div128CallSkipClose covers Div128FinalAssembly + Div128KnuthLower +
-- Div128QuotientBounds → KnuthTheoremB → {DivN4Overestimate,
-- MaxTrialVacuity → CLZLemmas → DivN4Lemmas, DenormLemmas}.
import EvmAsm.Evm64.EvmWordArith.Div128CallSkipClose

-- ModBridgeAssemble covers ModBridgeUtop → Val256ModBridge.
import EvmAsm.Evm64.EvmWordArith.ModBridgeAssemble

-- Standalone leaves:
import EvmAsm.Evm64.EvmWordArith.SkipBorrowExtract
import EvmAsm.Evm64.EvmWordArith.DivN4DoubleAddback
import EvmAsm.Evm64.EvmWordArith.AddbackBorrowExtract
import EvmAsm.Evm64.EvmWordArith.AddbackPinning
import EvmAsm.Evm64.EvmWordArith.Div128Shift0
