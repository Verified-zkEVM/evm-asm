/-
  EvmAsm.Evm64

  Root import file for the 64-bit EVM opcode implementations (RV64IM).
-/

-- Foundations (Basic and Stack are transitively imported by every
-- opcode Program file via Stack → Basic).
import EvmAsm.Evm64.CodeRegion

-- Accelerator C ABI bridges (zkvm_accelerators.h)
import EvmAsm.Evm64.Accelerators.Types
import EvmAsm.Evm64.Accelerators.Status
import EvmAsm.Evm64.Accelerators.SyscallIds
import EvmAsm.Evm64.Accelerators.Dispatch
import EvmAsm.Evm64.Accelerators.Coverage

-- Stack operations
import EvmAsm.Evm64.Pop
import EvmAsm.Evm64.Push0
import EvmAsm.Evm64.Push
import EvmAsm.Evm64.Dup
import EvmAsm.Evm64.Swap

-- Bitwise operations
import EvmAsm.Evm64.And
import EvmAsm.Evm64.Or
import EvmAsm.Evm64.Xor
import EvmAsm.Evm64.Not

-- Arithmetic (Add.Spec transitively imports EvmWordArith)
import EvmAsm.Evm64.Add
import EvmAsm.Evm64.Sub

-- EvmWordArith umbrella — pulls in helpers used by DivMod V4.
-- Most leaves are already transitively reached via Add/DivMod; this
-- import wires the remaining stragglers so they participate in the
-- visible module graph.
import EvmAsm.Evm64.EvmWordArith

-- Comparisons (Lt.Spec transitively imports Compare.LimbSpec)
import EvmAsm.Evm64.Lt
import EvmAsm.Evm64.Gt
import EvmAsm.Evm64.Eq
import EvmAsm.Evm64.IsZero
import EvmAsm.Evm64.Slt
import EvmAsm.Evm64.Sgt

-- Shifts
import EvmAsm.Evm64.Shift

-- Byte and SignExtend
import EvmAsm.Evm64.Byte
import EvmAsm.Evm64.SignExtend

-- Multiply
import EvmAsm.Evm64.Multiply

-- Exp (skeleton — GH #92, square-and-multiply over 256-bit exponent)
import EvmAsm.Evm64.Exp

-- DivMod (Knuth Algorithm D)
import EvmAsm.Evm64.DivMod.TrialPredicatesN4
import EvmAsm.Evm64.DivMod
import EvmAsm.Evm64.DivMod.Callable
import EvmAsm.Evm64.DivMod.CallableBzeroV4
import EvmAsm.Evm64.DivMod.LimbSpec.Div128Step1FullV5

-- SDIV / SMOD skeletons (GH #90, signed division/modulo)
import EvmAsm.Evm64.SDiv
import EvmAsm.Evm64.SMod

-- ADDMOD / MULMOD skeletons (GH #91)
import EvmAsm.Evm64.AddMod
import EvmAsm.Evm64.MulMod

-- Calling convention (LP64)
import EvmAsm.Evm64.CallingConvention

-- Execution-context structure (#100 slice 1; envIs assertion lands in slice 3)
import EvmAsm.Evm64.Environment
import EvmAsm.Evm64.Environment.Layout
import EvmAsm.Evm64.Environment.Assertion
import EvmAsm.Evm64.ReturnData.Basic
import EvmAsm.Evm64.ReturnData.CopyArgs
import EvmAsm.Evm64.ReturnData.CopyArgsStackDecode
import EvmAsm.Evm64.ReturnData.CopyExec
import EvmAsm.Evm64.ReturnData.CopyMemory
import EvmAsm.Evm64.Env.Field
import EvmAsm.Evm64.Env.Semantics
import EvmAsm.Evm64.Env.Program
import EvmAsm.Evm64.Env.Spec
import EvmAsm.Evm64.Env.StackSpec
import EvmAsm.Evm64.Env.Wrappers
import EvmAsm.Evm64.CallArgs
import EvmAsm.Evm64.CallArgsStackDecode
import EvmAsm.Evm64.CreateArgs
import EvmAsm.Evm64.CreateArgsStackDecode
import EvmAsm.Evm64.LogArgs
import EvmAsm.Evm64.LogArgsStackDecode
import EvmAsm.Evm64.TerminatingArgs
import EvmAsm.Evm64.TerminatingArgsStackDecode

-- Static gas schedule (#117)
import EvmAsm.Evm64.Gas
import EvmAsm.Evm64.Env.Gas
import EvmAsm.Evm64.StorageGas
import EvmAsm.Evm64.StorageAccess
import EvmAsm.Evm64.StorageAccessWarm
import EvmAsm.Evm64.StorageAccessOutcome
import EvmAsm.Evm64.StorageArgs
import EvmAsm.Evm64.StorageAssertions

-- Opcode dispatch surface (#106)
import EvmAsm.Evm64.Dispatch
import EvmAsm.Evm64.Dispatch.Program
import EvmAsm.Evm64.Dispatch.EntrySpec
import EvmAsm.Evm64.Dispatch.EntryAddrBridge
import EvmAsm.Evm64.Dispatch.TailSpec
import EvmAsm.Evm64.Dispatch.Compose
import EvmAsm.Evm64.Dispatch.Spec
import EvmAsm.Evm64.JumpTable
import EvmAsm.Evm64.ExecutableSpecOpcodeBridge
import EvmAsm.Evm64.HandlerTable
import EvmAsm.Evm64.HandlerTableByte
import EvmAsm.Evm64.HandlerTableCompose
import EvmAsm.Evm64.StackHandlers
import EvmAsm.Evm64.Code.Basic
import EvmAsm.Evm64.Code.CopyArgs
import EvmAsm.Evm64.Code.CopyArgsStackDecode
import EvmAsm.Evm64.Code.CopyExec
import EvmAsm.Evm64.Code.CopyMemory
import EvmAsm.Evm64.CodeHandlers
import EvmAsm.Evm64.PushHandlers
import EvmAsm.Evm64.ControlHandlers
import EvmAsm.Evm64.MemoryHandlers
import EvmAsm.Evm64.TerminatingHandlers
import EvmAsm.Evm64.DupSwapHandlers
import EvmAsm.Evm64.CalldataHandlers
import EvmAsm.Evm64.ShiftHandlers
import EvmAsm.Evm64.EnvHandlers
import EvmAsm.Evm64.ReturnDataHandlers
import EvmAsm.Evm64.ComparisonHandlers
import EvmAsm.Evm64.BitwiseHandlers
import EvmAsm.Evm64.ArithmeticHandlers
import EvmAsm.Evm64.SupportedHandlers
import EvmAsm.Evm64.SupportedHandlerByte
import EvmAsm.Evm64.SupportedLoopBridge
import EvmAsm.Evm64.InterpreterFetchProgram
import EvmAsm.Evm64.HandlerLoopBridge
import EvmAsm.Evm64.TerminatingLoopBridge
import EvmAsm.Evm64.HandlerLoopSimulationBridge
import EvmAsm.Evm64.InterpreterLoop
import EvmAsm.Evm64.InterpreterLoopStatus
import EvmAsm.Evm64.InterpreterSimulation
import EvmAsm.Evm64.InterpreterLoopSimulation
import EvmAsm.Evm64.InterpreterTrace
import EvmAsm.Evm64.InterpreterTraceSimulation
import EvmAsm.Evm64.InterpreterLoopCompose
import EvmAsm.Evm64.InterpreterExecutableFetchBridge
import EvmAsm.Evm64.InterpreterExecutableStepBridge

-- Precompile dispatch surface (#116)
import EvmAsm.Evm64.Precompile
import EvmAsm.Evm64.PrecompileResult
import EvmAsm.Evm64.PrecompileDispatch

-- EVM memory model (issue #99)
import EvmAsm.Evm64.Memory
import EvmAsm.Evm64.StateAssertions
import EvmAsm.Evm64.MptAssertions
import EvmAsm.Evm64.AccountRlp
import EvmAsm.Evm64.AccountFieldExtractSpec
import EvmAsm.Evm64.AccountAccessorSpec
import EvmAsm.Evm64.AccountAccessorTopSpec
import EvmAsm.Evm64.AccountBalanceHelperSpec
import EvmAsm.Evm64.WitnessAssertions
import EvmAsm.Evm64.MemoryGas
import EvmAsm.Evm64.KeccakArgs
import EvmAsm.Evm64.KeccakArgsStackDecode
import EvmAsm.Evm64.LogGas
import EvmAsm.Evm64.LogArgsGas
import EvmAsm.Evm64.TerminatingGas
import EvmAsm.Evm64.EvmState
import EvmAsm.Evm64.Termination
import EvmAsm.Evm64.MSize
import EvmAsm.Evm64.MStore8
import EvmAsm.Evm64.MStore
import EvmAsm.Evm64.MLoad

-- Calldata helpers (issue #104)
import EvmAsm.Evm64.Calldata.Basic
import EvmAsm.Evm64.Calldata.LoadArgs
import EvmAsm.Evm64.Calldata.LoadArgsStackDecode
import EvmAsm.Evm64.Calldata.Size
import EvmAsm.Evm64.Calldata.SizeProgram
import EvmAsm.Evm64.Calldata.SizeSpec
import EvmAsm.Evm64.Calldata.LoadProgram
import EvmAsm.Evm64.Calldata.LoadFullProgram
import EvmAsm.Evm64.Calldata.LoadStackCode
import EvmAsm.Evm64.Calldata.LoadWindowWord
import EvmAsm.Evm64.Calldata.LoadDispatch
import EvmAsm.Evm64.Calldata.Region
import EvmAsm.Evm64.Calldata.LoadWindowArm
import EvmAsm.Evm64.Calldata.LoadSpec
import EvmAsm.Evm64.Calldata.StageWindow
import EvmAsm.Evm64.Calldata.StageProgram
import EvmAsm.Evm64.Calldata.StageSpec
import EvmAsm.Evm64.Calldata.CopyArgs
import EvmAsm.Evm64.Calldata.CopyArgsStackDecode
import EvmAsm.Evm64.Calldata.CopyExec
import EvmAsm.Evm64.Calldata.CopyMemory
import EvmAsm.Evm64.Calldata.CopyProgram
import EvmAsm.Evm64.Calldata.CopySpec
import EvmAsm.Evm64.Calldata.CopyLoopSpec
