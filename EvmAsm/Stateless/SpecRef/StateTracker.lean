/-
  EvmAsm.Stateless.SpecRef.StateTracker

  Port of `execution-specs/src/ethereum/forks/amsterdam/state_tracker.py`
  (`@tests-zkevm@v0.5.0`, `bd8c673`) — the diff-tracking state layer of
  the EVM core (bead `evm-asm-s1d19.5`, Stack C):

  * `BlockState` / `TransactionState` (classes of the same names)
  * reads: `get_pre_state_account_optional`, `get_pre_state_account`,
    `get_account_optional`, `get_account`, `get_code`, `get_storage`,
    `get_storage_original`, `get_transient_storage`
  * predicates: `account_exists`, `account_deployable`,
    `account_has_storage`, `account_exists_and_is_empty`,
    `is_account_alive`
  * writes: `set_account`, `set_storage`, `destroy_account`,
    `clear_account_preserving_balance`, `destroy_storage`,
    `mark_account_created`, `set_transient_storage`, `modify_state`,
    `move_ether`, `create_ether`, `set_account_balance`,
    `increment_nonce`, `set_code`
  * snapshot/rollback: `copy_tx_state`, `restore_tx_state`
  * lifecycle: `incorporate_tx_into_block` (the BAL half lives in
    `BlockAccessLists.lean`), `extract_block_diff`,
    `get_witness_ancestors`, `track_ancestor_access`
  * `EMPTY_ACCOUNT` (`ethereum/state.py`,
    `execution-specs/src/ethereum/state.py` constant `EMPTY_ACCOUNT`)
    and `BlockDiff` (class `BlockDiff`)

  ## Modeling notes

  * The Python trackers are mutable dataclasses threaded through every
    VM function; here the whole tracker is the state of the monad
    `TxM α := StateT TransactionState (Except SpecError) α` (the
    `BlockState` parent lives inside the `TransactionState`).
    `pre_state` reads go through the authenticated witness layer
    (`WitnessReads.lean`), whose rejections propagate in the `Except`.
  * Python `dict`s become insertion-ordered assoc lists (update keeps
    position, new keys append) and `set`s append-ordered dedup lists —
    every consumer either checks membership or sorts before use
    (`BlockAccessLists.lean`), so set order is unobservable.
  * **Rollback sharing**: `copy_tx_state` deep-copies the write maps
    and transient storage but SHARES `account_reads`/`storage_reads`/
    `code_reads`/`created_accounts` (reads survive rollback, for BAL).
    Immutably: `restore_tx_state` takes the write fields from the
    snapshot and keeps the current read fields — same observable
    result.
  * `move_ether`'s insufficient-balance `AssertionError` is a
    rejection (`SpecError.stateError`); the accepting path never hits
    it (callers check balances first).
-/

import EvmAsm.Stateless.SpecRef.WitnessReads

namespace EvmAsm.Stateless.SpecRef

/-- `EMPTY_ACCOUNT` (`ethereum/state.py`). -/
def EMPTY_ACCOUNT : Account := { nonce := 0, balance := 0, codeHash := EMPTY_CODE_HASH }

/-! ## Assoc-list dict/set helpers (Python `dict`/`set` semantics) -/

/-- Dict write: update keeps position, new key appends. -/
def dictSet [BEq κ] (d : List (κ × α)) (k : κ) (v : α) : List (κ × α) :=
  if d.any (·.1 == k) then d.map (fun p => if p.1 == k then (k, v) else p)
  else d ++ [(k, v)]

def dictGet? [BEq κ] (d : List (κ × α)) (k : κ) : Option α :=
  (d.find? (·.1 == k)).map (·.2)

def dictHas [BEq κ] (d : List (κ × α)) (k : κ) : Bool := d.any (·.1 == k)

def dictDel [BEq κ] (d : List (κ × α)) (k : κ) : List (κ × α) :=
  d.filter (·.1 != k)

/-- Set add: dedup, append order. -/
def setAdd [BEq α] (s : List α) (x : α) : List α :=
  if s.contains x then s else s ++ [x]

/-- Set union (`update`): add each in order. -/
def setUnion [BEq α] (s t : List α) : List α := t.foldl setAdd s

/-! ## `BlockState` / `TransactionState` -/

abbrev StorageKey := Address × Bytes32
abbrev CodeRead := Address × Hash32

/-- `BlockState` (class `BlockState`): committed transaction-level
    changes accumulated across a block. -/
structure BlockState where
  preState : WitnessPreState
  accountReads : List Address := []
  accountWrites : List (Address × Option Account) := []
  storageReads : List StorageKey := []
  storageWrites : List (Address × List (Bytes32 × U256)) := []
  codeReads : List CodeRead := []
  codeWrites : List (Hash32 × Bytes) := []
  oldestAncestorOffset : Option Uint := none
  /-- Modeling-only (not a Python field): the addresses whose reads
      reached the witness (`ws.get_account_optional` / `ws.get_storage`
      / `ws.account_has_storage` fall-throughs) — exactly the keys the
      Python `WitnessState._storage_root_cache` holds at block end,
      which `compute_state_root_and_trie_changes` observes (its
      `cache₀`; values are the deterministic `_storage_root_of`).
      See `WitnessStateRoot.lean` `cacheFromReads`. -/
  preStateReads : List Address := []

/-- `TransactionState` (class `TransactionState`): in-flight changes
    within a single transaction. -/
structure TransactionState where
  parent : BlockState
  accountReads : List Address := []
  accountWrites : List (Address × Option Account) := []
  storageReads : List StorageKey := []
  storageWrites : List (Address × List (Bytes32 × U256)) := []
  codeReads : List CodeRead := []
  codeWrites : List (Hash32 × Bytes) := []
  createdAccounts : List Address := []
  transientStorage : List (StorageKey × U256) := []

/-- The transaction-state monad: every `state_tracker.py` function
    threads the mutable trackers; rejections propagate in `Except`. -/
abbrev TxM (α : Type) := StateT TransactionState (Except SpecError) α

/-- `BlockDiff` (`ethereum/state.py`, class `BlockDiff`). -/
structure BlockDiff where
  accountChanges : List (Address × Option Account)
  storageChanges : List (Address × List (Bytes32 × U256))
  codeChanges : List (Hash32 × Bytes)

/-! ## Reads -/

/-- Record a witness-reaching read (see `BlockState.preStateReads`). -/
def recordPreStateRead (address : Address) : TxM Unit :=
  modify (fun ts => { ts with parent :=
    { ts.parent with preStateReads := setAdd ts.parent.preStateReads address } })

/-- `get_pre_state_account_optional(tx_state, address)`. -/
def get_pre_state_account_optional (address : Address) : TxM (Option Account) := do
  modify (fun ts => { ts with accountReads := setAdd ts.accountReads address })
  let ts ← get
  match dictGet? ts.parent.accountWrites address with
  | some acct => pure acct
  | none => do
      recordPreStateRead address
      StateT.lift (get_account_optional ts.parent.preState address)

/-- `get_pre_state_account(tx_state, address)`. -/
def get_pre_state_account (address : Address) : TxM Account := do
  pure ((← get_pre_state_account_optional address).getD EMPTY_ACCOUNT)

/-- `get_account_optional(tx_state, address)` — NB shadows the
    `WitnessReads` name inside `TxM`; the tx-write layer first. -/
def getAccountOptional (address : Address) : TxM (Option Account) := do
  modify (fun ts => { ts with accountReads := setAdd ts.accountReads address })
  let ts ← get
  match dictGet? ts.accountWrites address with
  | some acct => pure acct
  | none => get_pre_state_account_optional address

/-- `get_account(tx_state, address)`. -/
def getAccount (address : Address) : TxM Account := do
  pure ((← getAccountOptional address).getD EMPTY_ACCOUNT)

/-- `get_code(tx_state, code_hash, address)`: tx code writes → block
    code writes → witness code DB (recording `code_reads` only on the
    pre-state fetch). -/
def getCode (code_hash : Hash32) (address : Address) : TxM Bytes := do
  if code_hash == EMPTY_CODE_HASH then pure [] else
  let ts ← get
  match dictGet? ts.codeWrites code_hash with
  | some code => pure code
  | none =>
  match dictGet? ts.parent.codeWrites code_hash with
  | some code => pure code
  | none => do
      modify (fun ts => { ts with codeReads := setAdd ts.codeReads (address, code_hash) })
      let ts ← get
      StateT.lift (get_code ts.parent.preState code_hash)

/-- `get_storage(tx_state, address, key)`. -/
def getStorage (address : Address) (key : Bytes32) : TxM U256 := do
  modify (fun ts => { ts with storageReads := setAdd ts.storageReads (address, key) })
  let ts ← get
  match (dictGet? ts.storageWrites address).bind (fun slots => dictGet? slots key) with
  | some v => pure v
  | none =>
  match (dictGet? ts.parent.storageWrites address).bind (fun slots => dictGet? slots key) with
  | some v => pure v
  | none => do
      recordPreStateRead address
      StateT.lift (get_storage ts.parent.preState address key)

/-- `get_storage_original(tx_state, address, key)`: the value before
    the current transaction (0 for accounts created in it). -/
def getStorageOriginal (address : Address) (key : Bytes32) : TxM U256 := do
  let ts ← get
  if ts.createdAccounts.contains address then pure 0 else
  match (dictGet? ts.parent.storageWrites address).bind (fun slots => dictGet? slots key) with
  | some v => pure v
  | none => do
      recordPreStateRead address
      StateT.lift (get_storage ts.parent.preState address key)

/-- `get_transient_storage(tx_state, address, key)`. -/
def getTransientStorage (address : Address) (key : Bytes32) : TxM U256 := do
  pure (((← get).transientStorage.find? (·.1 == (address, key))).map (·.2) |>.getD 0)

/-! ## Predicates -/

/-- `account_exists(tx_state, address)`. -/
def accountExists (address : Address) : TxM Bool := do
  pure (← getAccountOptional address).isSome

/-- `account_has_storage(tx_state, address)` — note the Python
    `storage_writes.get(address)` truthiness: an address mapped to an
    EMPTY slot dict does not count. -/
def accountHasStorage (address : Address) : TxM Bool := do
  let ts ← get
  if ((dictGet? ts.storageWrites address).getD []).length > 0 then pure true
  else if ((dictGet? ts.parent.storageWrites address).getD []).length > 0 then pure true
  else do
    recordPreStateRead address
    StateT.lift (account_has_storage ts.parent.preState address)

/-- `account_deployable(tx_state, address)`. -/
def accountDeployable (address : Address) : TxM Bool := do
  let account ← getAccount address
  if account.nonce ≠ 0 || account.codeHash ≠ EMPTY_CODE_HASH then pure false
  else pure !(← accountHasStorage address)

/-- `account_exists_and_is_empty(tx_state, address)`. -/
def accountExistsAndIsEmpty (address : Address) : TxM Bool := do
  match ← getAccountOptional address with
  | some a => pure (a.nonce == 0 && a.codeHash == EMPTY_CODE_HASH && a.balance == 0)
  | none => pure false

/-- `is_account_alive(tx_state, address)`. -/
def isAccountAlive (address : Address) : TxM Bool := do
  match ← getAccountOptional address with
  | some a => pure (a != EMPTY_ACCOUNT)
  | none => pure false

/-! ## Writes -/

/-- `set_account(tx_state, address, account)`. -/
def setAccount (address : Address) (account : Option Account) : TxM Unit :=
  modify (fun ts => { ts with accountWrites := dictSet ts.accountWrites address account })

/-- `set_storage(tx_state, address, key, value)`; the Python `assert`
    (account must exist) is a rejection. -/
def setStorage (address : Address) (key : Bytes32) (value : U256) : TxM Unit := do
  if (← getAccountOptional address).isNone then
    throw (.stateError "set_storage on non-existent account")
  modify (fun ts =>
    let slots := dictSet ((dictGet? ts.storageWrites address).getD []) key value
    { ts with storageWrites := dictSet ts.storageWrites address slots })

/-- `destroy_storage(tx_state, address)`: writes convert to reads
    before deletion (created-then-destroyed accesses stay in the BAL). -/
def destroyStorage (address : Address) : TxM Unit :=
  modify (fun ts =>
    match dictGet? ts.storageWrites address with
    | none => ts
    | some slots =>
        { ts with
          storageReads := slots.foldl (fun rs (k, _) => setAdd rs (address, k)) ts.storageReads
          storageWrites := dictDel ts.storageWrites address })

/-- `destroy_account(tx_state, address)`. -/
def destroyAccount (address : Address) : TxM Unit := do
  destroyStorage address
  setAccount address none

/-- `account_exists_and_is_empty` post-check + destroy — the tail of
    `modify_state`. -/
def modifyState (address : Address) (f : Account → Account) : TxM Unit := do
  setAccount address (some (f (← getAccount address)))
  if ← accountExistsAndIsEmpty address then
    destroyAccount address

/-- `clear_account_preserving_balance(tx_state, address)`. -/
def clearAccountPreservingBalance (address : Address) : TxM Unit := do
  destroyStorage address
  modifyState address (fun a => { a with nonce := 0, codeHash := EMPTY_CODE_HASH })

/-- `mark_account_created(tx_state, address)`. -/
def markAccountCreated (address : Address) : TxM Unit :=
  modify (fun ts => { ts with createdAccounts := setAdd ts.createdAccounts address })

/-- `set_transient_storage(tx_state, address, key, value)` (zero pops). -/
def setTransientStorage (address : Address) (key : Bytes32) (value : U256) : TxM Unit :=
  modify (fun ts =>
    if value == 0 then
      { ts with transientStorage := ts.transientStorage.filter (·.1 != (address, key)) }
    else
      { ts with transientStorage := dictSet ts.transientStorage (address, key) value })

/-- `move_ether(tx_state, sender, recipient, amount)`; the
    insufficient-balance `AssertionError` rejects. -/
def moveEther (sender_address recipient_address : Address) (amount : U256) : TxM Unit := do
  let sender ← getAccount sender_address
  if sender.balance < amount then
    throw (.stateError "move_ether: insufficient balance")
  modifyState sender_address (fun a => { a with balance := a.balance - amount })
  modifyState recipient_address (fun a => { a with balance := a.balance + amount })

/-- `create_ether(tx_state, address, amount)`. -/
def createEther (address : Address) (amount : U256) : TxM Unit :=
  modifyState address (fun a => { a with balance := a.balance + amount })

/-- `set_account_balance(tx_state, address, amount)`. -/
def setAccountBalance (address : Address) (amount : U256) : TxM Unit :=
  modifyState address (fun a => { a with balance := amount })

/-- `increment_nonce(tx_state, address)`. -/
def incrementNonce (address : Address) : TxM Unit :=
  modifyState address (fun a => { a with nonce := a.nonce + 1 })

/-- `set_code(tx_state, address, code)`. -/
def setCode (address : Address) (code : Bytes) : TxM Unit := do
  let code_hash := keccak256 code
  if code_hash != EMPTY_CODE_HASH then
    modify (fun ts => { ts with codeWrites := dictSet ts.codeWrites code_hash code })
  modifyState address (fun a => { a with codeHash := code_hash })

/-! ## Snapshot / rollback -/

/-- `copy_tx_state(tx_state)`: the whole record IS the snapshot (the
    shared-reference read sets are handled by `restoreTxState`). -/
def copyTxState : TxM TransactionState := get

/-- `restore_tx_state(tx_state, snapshot)`: restore the write maps and
    transient storage; reads and `created_accounts` keep accumulating. -/
def restoreTxState (snapshot : TransactionState) : TxM Unit :=
  modify (fun ts =>
    { ts with accountWrites := snapshot.accountWrites
              storageWrites := snapshot.storageWrites
              codeWrites := snapshot.codeWrites
              transientStorage := snapshot.transientStorage })

/-! ## Lifecycle -/

/-- The read/write-merging half of `incorporate_tx_into_block` (the
    `update_builder_from_tx` call happens first — see
    `BlockAccessLists.lean`, which wraps both). -/
def mergeTxIntoBlock : TxM Unit :=
  modify (fun ts =>
    let block := ts.parent
    let block :=
      { block with
        storageReads := setUnion block.storageReads ts.storageReads
        accountReads := setUnion block.accountReads ts.accountReads
        codeReads := setUnion block.codeReads ts.codeReads
        accountWrites := ts.accountWrites.foldl (fun d (a, acct) => dictSet d a acct)
          block.accountWrites
        storageWrites := ts.storageWrites.foldl (fun d (a, slots) =>
          dictSet d a (slots.foldl (fun s (k, v) => dictSet s k v)
            ((dictGet? d a).getD []))) block.storageWrites
        codeWrites := ts.codeWrites.foldl (fun d (h, c) => dictSet d h c)
          block.codeWrites }
    { parent := block })

/-- `extract_block_diff(block_state)`. -/
def extract_block_diff (block_state : BlockState) : BlockDiff :=
  { accountChanges := block_state.accountWrites
    storageChanges := block_state.storageWrites
    codeChanges := block_state.codeWrites }

/-- `get_witness_ancestors(block_headers, oldest_ancestor_offset)`. -/
def get_witness_ancestors (block_headers : List Bytes)
    (oldest_ancestor_offset : Option Uint) : List Bytes :=
  match oldest_ancestor_offset with
  | none => []
  | some off =>
      -- Python `block_headers[-off:]`: `-0` slices the whole list.
      if off == 0 then block_headers
      else block_headers.drop (block_headers.length - off)

/-- `track_ancestor_access(block_state, offset)`. -/
def trackAncestorAccess (offset : Uint) : TxM Unit :=
  modify (fun ts =>
    { ts with parent :=
      { ts.parent with oldestAncestorOffset :=
          match ts.parent.oldestAncestorOffset with
          | none => some offset
          | some cur => some (max cur offset) } })

end EvmAsm.Stateless.SpecRef
