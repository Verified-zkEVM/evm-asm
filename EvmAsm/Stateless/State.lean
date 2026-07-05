/-
  EvmAsm.Stateless.State

  Umbrella for the world-state machinery of the stateless guest.
  Mirrors the Python `WitnessState` + `BlockState` + `TransactionState`
  layered overlays from `forks/amsterdam/state.py`,
  `state_tracker.py`, and `witness_state.py`.

  ## Architecture overview (Python reference)

      PreState (≈ WitnessState):
        - read-only base, backed by witness.state via MPT walk
        - keys: keccak256(address) -> Account
                keccak256(slot) -> storage value

      BlockState:
        - copy-on-write overlay over PreState
        - accumulates account / storage / code mutations during
          a block's STF
        - read paths: tx_state.snapshot ∪ block_state ∪ pre_state

      TransactionState:
        - per-tx overlay over BlockState
        - rolls back on REVERT / failure

      BlockDiff (output of apply_body):
        - account_changes : dict[Address, AccountDiff]
        - storage_changes : dict[(Address, Slot), Value]
        - code_changes    : dict[CodeHash, Code]

      compute_state_root_and_trie_changes:
        - input: PreState + BlockDiff
        - output: new state_root via incremental MPT updates

  ## Subtree

  - `Account.lean`     — RLP-decode/encode account record
                         (nonce, balance, storageRoot, codeHash).
  - `Storage.lean`     — slot get/set, copy-on-write tracker.
  - `PreState.lean`    — bundle (node_db, code_db, state_root)
                         from Witness/.
  - `BlockState.lean`  — read/write sets for the current block.
  - `TxState.lean`     — per-tx rollback frame.
  - `Diff.lean`        — BlockDiff record.
  - `StateRoot.lean`   — compute_state_root_and_trie_changes:
                         apply BlockDiff to PreState's MPT and
                         re-hash to produce new state_root.
  - `Spec.lean`        — cpsTriple placeholders.

  All sub-files are scaffolds in PR-K10.
-/

import EvmAsm.Stateless.State.Account
import EvmAsm.Stateless.State.AccountAssertions
import EvmAsm.Stateless.State.Storage
import EvmAsm.Stateless.State.PreState
import EvmAsm.Stateless.State.BlockState
import EvmAsm.Stateless.State.TxState
import EvmAsm.Stateless.State.Diff
import EvmAsm.Stateless.State.StateRoot
import EvmAsm.Stateless.State.Spec
