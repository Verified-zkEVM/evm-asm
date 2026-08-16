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
import EvmAsm.Stateless.SSZ.Decode.ActiveForkSAsm
import EvmAsm.Stateless.SSZ.Encode.Program
import EvmAsm.Stateless.SSZ.HashTreeRoot.Program
import EvmAsm.Stateless.SSZ.HashTreeRoot.ZeroHashes
import EvmAsm.Stateless.SSZ.HashTreeRoot.Merkleize
import EvmAsm.Stateless.SSZ.HashTreeRoot.MerkleizeFull
import EvmAsm.Stateless.SSZ.HashTreeRoot.PackBytes
import EvmAsm.Stateless.SSZ.HashTreeRoot.HashBytes
import EvmAsm.Stateless.SSZ.HashTreeRoot.ListByteList
import EvmAsm.Stateless.SSZ.HashTreeRoot.ExecutionWitness
import EvmAsm.Stateless.VM.Precompiles
import EvmAsm.Stateless.Headers.BlockHash
import EvmAsm.Stateless.State.AccountAssertions
import EvmAsm.Stateless.State.WriteMapAssertions
import EvmAsm.Stateless.State.AccountWriteUpsert
import EvmAsm.Stateless.State.UndoJournalAssertions
import EvmAsm.Stateless.State.StorageReadPath
import EvmAsm.Stateless.Entry
import EvmAsm.Stateless.EntrySpec
import EvmAsm.Stateless.SpecRef
