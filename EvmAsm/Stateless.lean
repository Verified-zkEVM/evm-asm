/-
  EvmAsm.Stateless

  Umbrella for the `run_stateless_guest` port of
  `execution-specs/src/ethereum/forks/amsterdam/stateless_guest.py`.

  PR1 (this commit): minimal compiling scaffold (memory layout +
  Unimplemented exit + top-level Entry stub + placeholder spec).
  Follow-up PRs flesh out the sub-trees listed in the plan file
  (`SSZ/`, `Headers/`, `Witness/`, `State/`, `ExecutionEngine/`,
  `Block/`, `Transaction/`, `VM/`, `Bridges/`).
-/

import EvmAsm.Stateless.MemoryLayout
import EvmAsm.Stateless.Unimplemented
import EvmAsm.Stateless.Constants
import EvmAsm.Stateless.SSZ.Decode.Program
import EvmAsm.Stateless.SSZ.Decode.ChainIdSAsm
import EvmAsm.Stateless.SSZ.Encode.Program
import EvmAsm.Stateless.SSZ.HashTreeRoot.Program
import EvmAsm.Stateless.SSZ.HashTreeRoot.ZeroHashes
import EvmAsm.Stateless.SSZ.HashTreeRoot.Merkleize
import EvmAsm.Stateless.SSZ.HashTreeRoot.MerkleizeFull
import EvmAsm.Stateless.SSZ.HashTreeRoot.PackBytes
import EvmAsm.Stateless.SSZ.HashTreeRoot.HashBytes
import EvmAsm.Stateless.SSZ.HashTreeRoot.ListByteList
import EvmAsm.Stateless.SSZ.HashTreeRoot.ExecutionWitness
import EvmAsm.Stateless.VM.Interpreter
import EvmAsm.Stateless.VM.Memory
import EvmAsm.Stateless.VM.Message
import EvmAsm.Stateless.VM.Precompiles
import EvmAsm.Stateless.VM.Spec
import EvmAsm.Stateless.VM.Stack
import EvmAsm.Stateless.Bridges.EcrecoverEcallBridge
import EvmAsm.Stateless.Bridges.EcrecoverInputBridge
import EvmAsm.Stateless.Bridges.EcrecoverResultBridge
import EvmAsm.Stateless.Bridges.Sha256EcallBridge
import EvmAsm.Stateless.ExecutionEngine.NewPayload
import EvmAsm.Stateless.ExecutionEngine.Requests
import EvmAsm.Stateless.ExecutionEngine.Spec
import EvmAsm.Stateless.Block.ApplyBody
import EvmAsm.Stateless.Block.Execute
import EvmAsm.Stateless.Block.Spec
import EvmAsm.Stateless.Block.ValidateHeader
import EvmAsm.Stateless.Transaction.Decode
import EvmAsm.Stateless.Transaction.Process
import EvmAsm.Stateless.Transaction.RecoverSender
import EvmAsm.Stateless.Transaction.Spec
import EvmAsm.Stateless.Transaction.Validate
import EvmAsm.Stateless.Witness.CodeDb.Program
import EvmAsm.Stateless.Witness.CodeDb.Spec
import EvmAsm.Stateless.Witness.MPT.Decode
import EvmAsm.Stateless.Witness.MPT.Get
import EvmAsm.Stateless.Witness.MPT.Root
import EvmAsm.Stateless.Witness.MPT.Set
import EvmAsm.Stateless.Witness.MPT.Spec
import EvmAsm.Stateless.Witness.MPT.Walk
import EvmAsm.Stateless.Witness.NodeDb.Lookup
import EvmAsm.Stateless.Witness.NodeDb.Program
import EvmAsm.Stateless.Witness.NodeDb.Spec
import EvmAsm.Stateless.Headers.BlockHash
import EvmAsm.Stateless.Headers.Decode
import EvmAsm.Stateless.Headers.KeccakArray
import EvmAsm.Stateless.Headers.KeccakChain
import EvmAsm.Stateless.Headers.ParentHash
import EvmAsm.Stateless.Headers.Spec
import EvmAsm.Stateless.Headers.Validate
import EvmAsm.Stateless.State.Account
import EvmAsm.Stateless.State.AccountAssertions
import EvmAsm.Stateless.State.WriteMapAssertions
import EvmAsm.Stateless.State.UndoJournalAssertions
import EvmAsm.Stateless.State.BlockState
import EvmAsm.Stateless.State.Diff
import EvmAsm.Stateless.State.PreState
import EvmAsm.Stateless.State.Spec
import EvmAsm.Stateless.State.StateRoot
import EvmAsm.Stateless.State.Storage
import EvmAsm.Stateless.State.TxState
import EvmAsm.Stateless.Entry
import EvmAsm.Stateless.EntrySpec
import EvmAsm.Stateless.SpecRef
