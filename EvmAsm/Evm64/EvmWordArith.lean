/-
  EvmAsm.Evm64.EvmWordArith

  Mathematical correctness lemmas connecting limb-level computations
  to 256-bit EvmWord operations. Used by stack-level specs.

  Re-exports all sub-modules for backwards compatibility. Many of the
  listed leaves transitively cover their Arithmetic / MultiLimb /
  Common prefix chain; see per-module comments below for the routing.
-/

-- Opcode-specific leaves that nothing else here imports:
module

public import EvmAsm.Evm64.EvmWordArith.IsZero
public import EvmAsm.Evm64.EvmWordArith.Eq
public import EvmAsm.Evm64.EvmWordArith.Comparison
public import EvmAsm.Evm64.EvmWordArith.ByteOps
public import EvmAsm.Evm64.EvmWordArith.LowMask
public import EvmAsm.Evm64.EvmWordArith.SignExtend
public import EvmAsm.Evm64.EvmWordArith.SDiv
public import EvmAsm.Evm64.EvmWordArith.SMod

-- MulCorrect covers Arithmetic → MultiLimb → Common.
public import EvmAsm.Evm64.EvmWordArith.MulCorrect

-- Pure EXP semantic target.
public import EvmAsm.Evm64.EvmWordArith.Exp

-- ADDMOD/MULMOD helper: 2^256 mod N as an EvmWord (#91).

-- Div128Shift0 → Div128CallSkipClose → {Div128FinalAssembly +
-- Div128KnuthLower + Div128QuotientBounds → KnuthTheoremB →
-- {DivN4Overestimate, MaxTrialVacuity → CLZLemmas → DivN4Lemmas,
-- DenormLemmas}, DivMod.LoopSemantic → {DivMulSubCarry, DivAddbackCarry}}.
-- `DivN4DoubleAddback` imports `DivN4Overestimate`, which in turn imports
-- `DivAccumulate`, covering
-- DivRemainderBound → DivAddbackLimb → DivMulSubLimb → DivLimbBridge →
-- DivBridge → Normalization → MulSubChain → Div128Lemmas → MultiLimb →
-- Div → Common.
public import EvmAsm.Evm64.EvmWordArith.Div128Shift0
public import EvmAsm.Evm64.EvmWordArith.DivCorrect
public import EvmAsm.Evm64.EvmWordArith.AddMod
public import EvmAsm.Evm64.EvmWordArith.MulHigh
public import EvmAsm.Evm64.EvmWordArith.MulMod

-- ModBridgeAssemble covers ModBridgeUtop → Val256ModBridge.
public import EvmAsm.Evm64.EvmWordArith.ModBridgeAssemble

-- Standalone leaves:
public import EvmAsm.Evm64.EvmWordArith.DivN4Lemmas
public import EvmAsm.Evm64.EvmWordArith.SkipBorrowExtract
public import EvmAsm.Evm64.EvmWordArith.DivN4DoubleAddback
public import EvmAsm.Evm64.EvmWordArith.DivN4SecondCarryGen
public import EvmAsm.Evm64.EvmWordArith.DivN4Carry2C3UTopPlusOne
public import EvmAsm.Evm64.EvmWordArith.DivN4SingleAddbackGen
public import EvmAsm.Evm64.EvmWordArith.DivN4BorrowRemainderLtGen
public import EvmAsm.Evm64.EvmWordArith.DivN4SingleAddbackVal256
public import EvmAsm.Evm64.EvmWordArith.DivN4DoubleAddbackVal256
public import EvmAsm.Evm64.EvmWordArith.DivN4IterConservationGen
public import EvmAsm.Evm64.EvmWordArith.DivN4RemainderLt
public import EvmAsm.Evm64.EvmWordArith.DivMulsubC3LeTwo
public import EvmAsm.Evm64.EvmWordArith.DivMulsubC3LeU4Plus2
public import EvmAsm.Evm64.EvmWordArith.DivN4C3LeUTopPlusOne
public import EvmAsm.Evm64.EvmWordArith.DivN3MaxOverestimate
public import EvmAsm.Evm64.EvmWordArith.DivN2MaxOverestimate
public import EvmAsm.Evm64.EvmWordArith.DivBltC3Invariant
public import EvmAsm.Evm64.EvmWordArith.DivMaxC3Invariant
public import EvmAsm.Evm64.EvmWordArith.DivC3InvariantIfBorrow
public import EvmAsm.Evm64.EvmWordArith.DivC3InvariantUnifiedCase
public import EvmAsm.Evm64.EvmWordArith.DivBltC3InvariantUnifiedCase
public import EvmAsm.Evm64.EvmWordArith.DivC3InvariantFromOverestimateUnreach
public import EvmAsm.Evm64.EvmWordArith.DivC3InvariantPlusTwoCase
public import EvmAsm.Evm64.EvmWordArith.DivBltC3InvariantPlusTwoCase
public import EvmAsm.Evm64.EvmWordArith.DivN3NormVStructure
public import EvmAsm.Evm64.EvmWordArith.DivN2NormVStructure
public import EvmAsm.Evm64.EvmWordArith.DivBltBridge
public import EvmAsm.Evm64.EvmWordArith.DivBltBridgeSpecializations
public import EvmAsm.Evm64.EvmWordArith.DivV4TrialOverestimate
public import EvmAsm.Evm64.EvmWordArith.DivV5TrialOverestimate
public import EvmAsm.Evm64.EvmWordArith.DivV4TrialFromExactQuotient
public import EvmAsm.Evm64.EvmWordArith.DivV4TrialVal256Composition
public import EvmAsm.Evm64.EvmWordArith.DivKnuthAEqualWindow
public import EvmAsm.Evm64.EvmWordArith.DivKnuthATopWindowFits
public import EvmAsm.Evm64.EvmWordArith.DivKnuthABTrivialComposition
public import EvmAsm.Evm64.EvmWordArith.DivKnuthABKnownConditions
public import EvmAsm.Evm64.EvmWordArith.DivC3InvariantTrivials
public import EvmAsm.Evm64.EvmWordArith.DivC3InvariantFromCarryNz
public import EvmAsm.Evm64.EvmWordArith.AddbackBorrowExtract
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Algorithm
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase2bNoFireBound
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase2bFireBound
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase1bBound
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Un21Bound
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Un21BoundDHiPow32
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.QuotientBounds
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Q0ddUBDHiPow32
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.NoWrapChainDHiPow32
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.WideRhatcUB
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Un21LevelUB
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Un21WideUHiCounterexample
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Q1ddUndershootFromWideUn21
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.V4QHatBoundCounterexamples
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.UpperBound
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.ExactQuotient
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Algorithm
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.CapBounds
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.NoWrap
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1d
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1cEuclidean
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Phase1bNoFireBound
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.V5BoundChainA
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.V5BoundChainB
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.V5BoundChainC
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.V5BoundChainD
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5Native
public import EvmAsm.Evm64.EvmWordArith.KnuthAFloorWindow
public import EvmAsm.Evm64.EvmWordArith.KnuthAFloorWindowN3
public import EvmAsm.Evm64.EvmWordArith.Div128CallSkipCloseV4

public section
