/-
  EvmAsm.Stateless.State.BlockState

  Copy-on-write overlay over PreState for the current block's
  STF. Mirrors Python's `BlockState` in
  `forks/amsterdam/state_tracker.py`. Accumulates account /
  storage / code mutations as transactions execute.

  ## Fields (Python reference)

      class BlockState:
          pre_state         : PreState         # immutable base
          account_changes   : dict[Address, Account]
          storage_changes   : dict[(Address, Slot), Value]
          code_changes      : dict[CodeHash, Bytes]
          accessed_accounts : set[Address]      # for warm/cold gas
          accessed_storage  : set[(Address, Slot)]

  ## Read chain

  `block_state.get_account(addr)`:
    if addr in account_changes: return account_changes[addr]
    return pre_state.get_account(addr)

  Same shape for `get_storage`. Reads from `code_changes` first,
  then `pre_state.get_code`.

  ## Write paths

  `block_state.set_account(addr, account)`:
    account_changes[addr] = account
    accessed_accounts.add(addr)

  ## End-of-block

  The accumulated diffs feed into `compute_state_root_and_trie_changes`
  (`StateRoot.lean`).

  ## Working RAM

  The aspirational port contract reserves `STATE_TRACKER_AREA`
  (`MemoryLayout.lean`), sized 4 MiB. The emitted guest's persistent
  storage path uses maps instead; only the separate transient-log sibling
  remains live at `0xa0830000`. Account changes are keyed by address (20
  bytes); storage changes by (address, slot) pairs (52 bytes); code changes
  by 32-byte hash.

  ## PR-K10 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.State.BlockState

-- TODO(stateless-state): expose BlockState record + read/write
-- helpers. Probably needs a hash-table representation for each
-- of the three change dicts.

end EvmAsm.Stateless.State.BlockState
