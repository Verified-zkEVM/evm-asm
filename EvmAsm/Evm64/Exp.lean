/-
  EvmAsm.Evm64.Exp

  Umbrella for the EXP opcode subtree (GH #92). Re-exports the top-level
  spec; downstream consumers should `import EvmAsm.Evm64.Exp` and not
  reach into sub-modules directly.

  AddrNormAttr is imported first (per AGENTS.md `register_simp_attr`
  ordering rule) so the `exp_addr` attribute exists when later modules
  attach lemmas to it.
-/

import EvmAsm.Evm64.Exp.AddrNormAttr
import EvmAsm.Evm64.Exp.Program
import EvmAsm.Evm64.Exp.Gas
import EvmAsm.Evm64.Exp.Args
import EvmAsm.Evm64.Exp.ArgsStackDecode
import EvmAsm.Evm64.Exp.LimbSpec
import EvmAsm.Evm64.Exp.MarshalPair
import EvmAsm.Evm64.Exp.SquaringCall
import EvmAsm.Evm64.Exp.SquaringCallSeq
import EvmAsm.Evm64.Exp.SquaringMarshalPairPost
import EvmAsm.Evm64.Exp.SquaringPairThenMulCall
import EvmAsm.Evm64.Exp.CondMulMarshalPair
import EvmAsm.Evm64.Exp.CondMulCall
import EvmAsm.Evm64.Exp.CondMulCallSeq
import EvmAsm.Evm64.Exp.CondMulPairThenMulCall
import EvmAsm.Evm64.Exp.AddrNorm
import EvmAsm.Evm64.Exp.Compose.Base
import EvmAsm.Evm64.Exp.Compose.EvmExpCode
import EvmAsm.Evm64.Exp.Compose.TopCodeSubs
import EvmAsm.Evm64.Exp.Compose.LoopCodeSpecs
import EvmAsm.Evm64.Exp.Compose.TopBoundaryBlocks
import EvmAsm.Evm64.Exp.TopPipelineShared
import EvmAsm.Evm64.Exp.SquaringMarshalShared
import EvmAsm.Evm64.Exp.SavedBitWithMulCondMarshalShared
import EvmAsm.Evm64.Exp.FullLoopShared
import EvmAsm.Evm64.Exp.Compose.SavedBitFullLoopCanonicalPrefix
import EvmAsm.Evm64.Exp.Compose.SavedBitFullLoopCanonical
import EvmAsm.Evm64.Exp.TwoMulCondShared
import EvmAsm.Evm64.Exp.Compose.SavedBitLoopBounds
import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryPrologue
import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryPrologueFixed
import EvmAsm.Evm64.Exp.Compose.SavedBitBaseTwoMulFixedIter
import EvmAsm.Evm64.Exp.Compose.SavedBitBaseTwoMulFixedIterLoop
import EvmAsm.Evm64.Exp.Compose.SavedBitBaseTwoMulFixedIterMerged
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedWithMul
import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryEntryFixedIterPre
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePosts
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterExits
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedMergedFramedStep
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedRelaxedBlock3Step
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostBridge
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostCountBridge
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostStateBridge
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostTailBounds
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostCases
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostFramedCases
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterReloadPointerPures
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostIterPreCases
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedExitBridge
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedRelaxedExitBridge
import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoopFixed
import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoopFixedEntryExists
import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoopFixedIterSpBounds
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedLoopInvariant
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedControlFrame
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedAccumulatorRun
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCount
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedBoolStep
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterState
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStatePre
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedInductionFramePre
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterPreNPost
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStepPost
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStep
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStepBounds
import EvmAsm.Evm64.Exp.SavedBitFixedIterStepShared
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoop
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoopReloadLimbFrames
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoopReloadTailFrames
import EvmAsm.Evm64.Exp.SavedBitFixedIterLoopShared
import EvmAsm.Evm64.Exp.SavedBitFixedInductionShared
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedReloadReshuffle
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedExpResidual
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedExpReadPrefix
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedReloadResidualRepartition
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedFinalResidualShared
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedBlock3ExitExp
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedExitVacuous
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedBoundaryLeftover
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedSaveRestoreCompose
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedHeadroomCompose
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedHeadroomFullLoop
import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryEpilogueBase
import EvmAsm.Evm64.Exp.Compose.SavedBitBoundarySeq
import EvmAsm.Evm64.Exp.Compose.SavedBitLoopEntry
import EvmAsm.Evm64.Exp.Compose.SavedBitEntryIterPreBridge
import EvmAsm.Evm64.Exp.Compose.SavedBitPrologueBodyCompose
import EvmAsm.Evm64.Exp.Compose.SavedBitLoopExit
import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoop
import EvmAsm.Evm64.Exp.Compose.SavedBitTwoMulSkipCanonical
import EvmAsm.Evm64.Exp.Compose.SavedBitTwoMulCondCanonical
import EvmAsm.Evm64.Exp.Compose.SavedBitIterPostDefs
import EvmAsm.Evm64.Exp.Compose.SavedBitIterPosts
import EvmAsm.Evm64.Exp.Compose.SavedBitIterPostPcFree
import EvmAsm.Evm64.Exp.Compose.SavedBitIterMerge
import EvmAsm.Evm64.Exp.Compose.SavedBitIterBridges
import EvmAsm.Evm64.Exp.Compose.SavedBitIterExitBridge
import EvmAsm.Evm64.Exp.Compose.SavedBitLoopBodyInd
import EvmAsm.Evm64.Exp.Compose.SavedBitSemanticStep
import EvmAsm.Evm64.Exp.Compose.SavedBitSemanticUnify
import EvmAsm.Evm64.Exp.Compose.SavedBitLoopBodyFromLoopPost
import EvmAsm.Evm64.Exp.Compose.MergedLoopInd
import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryEntryBody
import EvmAsm.Evm64.Exp.Layout
import EvmAsm.Evm64.Exp.Spec
import EvmAsm.Evm64.Exp.StackExecutionBridge
