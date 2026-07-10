/-
  EvmAsm.Stateless.SpecRef.BlockAccessLists

  Port of
  `execution-specs/src/ethereum/forks/amsterdam/block_access_lists.py`
  (`@tests-zkevm@v0.5.0`, `bd8c673`) — the EIP-7928 Block Access List
  builder (bead `evm-asm-s1d19.5`, Stack C):

  * the BAL dataclasses (classes `StorageChange`, `BalanceChange`,
    `NonceChange`, `CodeChange`, `SlotChanges`, `AccountChanges`,
    `AccountData`, `BlockAccessListBuilder`)
  * `ensure_account`, `add_storage_write`, `add_storage_read`,
    `add_balance_change`, `add_nonce_change`, `add_code_change`,
    `add_touched_account` (functions of the same names)
  * `_build_from_builder`, `_get_pre_tx_account`, `_get_pre_tx_storage`,
    `update_builder_from_tx`, `build_block_access_list`,
    `hash_block_access_list`, `validate_block_access_list_gas_limit`
    (functions of the same names)

  plus `incorporate_tx_into_block` (`state_tracker.py`, function
  `incorporate_tx_into_block`), which composes
  `update_builder_from_tx` with the merge half in `StateTracker.lean`.

  ## Modeling notes

  * Builder dicts/sets are insertion-ordered assoc/dedup lists (see
    `StateTracker.lean`); `_build_from_builder` sorts every output
    axis (addresses, slots, reads, per-type change lists by
    block-access index), so container order is unobservable in the
    final BAL and its hash.  Python `sorted` is stable — mirrored by
    `List.mergeSort`.
  * `update_builder_from_tx`'s pre-tx lookups (`_get_pre_tx_account` /
    `_get_pre_tx_storage`) read the witness DIRECTLY (no read
    recording); the code-change path reads through the tracker
    (`getCode`, recording `code_reads`) exactly as Python does.
-/

import EvmAsm.Stateless.SpecRef.StateTracker
import EvmAsm.Stateless.SpecRef.WitnessStateRoot
import EvmAsm.Stateless.SpecRef.Gas

namespace EvmAsm.Stateless.SpecRef

open EvmAsm.EL.RLP (RLPItem)

/-! ## BAL dataclasses -/

/-- `StorageChange` (class `StorageChange`). -/
structure StorageChange where
  blockAccessIndex : Nat
  newValue : U256
  deriving Repr, BEq

/-- `BalanceChange` (class `BalanceChange`). -/
structure BalanceChange where
  blockAccessIndex : Nat
  postBalance : U256
  deriving Repr, BEq

/-- `NonceChange` (class `NonceChange`). -/
structure NonceChange where
  blockAccessIndex : Nat
  newNonce : U64
  deriving Repr, BEq

/-- `CodeChange` (class `CodeChange`). -/
structure CodeChange where
  blockAccessIndex : Nat
  newCode : Bytes
  deriving Repr, BEq

/-- `SlotChanges` (class `SlotChanges`). -/
structure SlotChanges where
  slot : U256
  changes : List StorageChange
  deriving Repr, BEq

/-- `AccountChanges` (class `AccountChanges`). -/
structure AccountChanges where
  address : Address
  storageChanges : List SlotChanges
  storageReads : List U256
  balanceChanges : List BalanceChange
  nonceChanges : List NonceChange
  codeChanges : List CodeChange
  deriving Repr, BEq

/-- `BlockAccessList` — `List[AccountChanges]`. -/
abbrev BlockAccessList := List AccountChanges

/-- `AccountData` (class `AccountData`): per-account builder state. -/
structure AccountData where
  storageChanges : List (U256 × List StorageChange) := []
  storageReads : List U256 := []
  balanceChanges : List BalanceChange := []
  nonceChanges : List NonceChange := []
  codeChanges : List CodeChange := []
  deriving Repr

/-- `BlockAccessListBuilder` (class `BlockAccessListBuilder`). -/
structure BlockAccessListBuilder where
  blockAccessIndex : Nat := 0
  accounts : List (Address × AccountData) := []
  deriving Repr

/-! ## Builder update functions -/

/-- `ensure_account(builder, address)`. -/
def ensure_account (b : BlockAccessListBuilder) (address : Address) :
    BlockAccessListBuilder :=
  if dictHas b.accounts address then b
  else { b with accounts := b.accounts ++ [(address, {})] }

private def modifyAccount (b : BlockAccessListBuilder) (address : Address)
    (f : AccountData → AccountData) : BlockAccessListBuilder :=
  let b := ensure_account b address
  { b with accounts := b.accounts.map (fun p =>
      if p.1 == address then (p.1, f p.2) else p) }

/-- Replace the entry with the same block-access index, else append —
    the shared update-or-append pattern of `add_storage_write` /
    `add_balance_change` / `add_code_change`. -/
private def upsertByIndex (changes : List α) (getIdx : α → Nat) (idx : Nat)
    (mk : α) : List α :=
  if changes.any (fun c => getIdx c == idx) then
    changes.map (fun c => if getIdx c == idx then mk else c)
  else changes ++ [mk]

/-- `add_storage_write(builder, address, slot, block_access_index,
    new_value)`. -/
def add_storage_write (b : BlockAccessListBuilder) (address : Address)
    (slot : U256) (idx : Nat) (new_value : U256) : BlockAccessListBuilder :=
  modifyAccount b address (fun ad =>
    let changes := (dictGet? ad.storageChanges slot).getD []
    let changes := upsertByIndex changes (·.blockAccessIndex) idx
      { blockAccessIndex := idx, newValue := new_value }
    { ad with storageChanges := dictSet ad.storageChanges slot changes })

/-- `add_storage_read(builder, address, slot)`. -/
def add_storage_read (b : BlockAccessListBuilder) (address : Address)
    (slot : U256) : BlockAccessListBuilder :=
  modifyAccount b address (fun ad =>
    { ad with storageReads := setAdd ad.storageReads slot })

/-- `add_balance_change(builder, address, block_access_index,
    post_balance)`. -/
def add_balance_change (b : BlockAccessListBuilder) (address : Address)
    (idx : Nat) (post_balance : U256) : BlockAccessListBuilder :=
  modifyAccount b address (fun ad =>
    let changes := upsertByIndex ad.balanceChanges (·.blockAccessIndex) idx
      { blockAccessIndex := idx, postBalance := post_balance }
    { ad with balanceChanges := changes })

/-- `add_nonce_change(builder, address, block_access_index, new_nonce)`
    — keeps the HIGHEST nonce per index. -/
def add_nonce_change (b : BlockAccessListBuilder) (address : Address)
    (idx : Nat) (new_nonce : U64) : BlockAccessListBuilder :=
  modifyAccount b address (fun ad =>
    if ad.nonceChanges.any (fun c => c.blockAccessIndex == idx) then
      { ad with nonceChanges := ad.nonceChanges.map (fun c =>
          if c.blockAccessIndex == idx && new_nonce > c.newNonce then
            { blockAccessIndex := idx, newNonce := new_nonce }
          else c) }
    else
      { ad with nonceChanges := ad.nonceChanges ++
          [{ blockAccessIndex := idx, newNonce := new_nonce }] })

/-- `add_code_change(builder, address, block_access_index, new_code)`. -/
def add_code_change (b : BlockAccessListBuilder) (address : Address)
    (idx : Nat) (new_code : Bytes) : BlockAccessListBuilder :=
  modifyAccount b address (fun ad =>
    let changes := upsertByIndex ad.codeChanges (·.blockAccessIndex) idx
      { blockAccessIndex := idx, newCode := new_code }
    { ad with codeChanges := changes })

/-- `add_touched_account(builder, address)`. -/
def add_touched_account (b : BlockAccessListBuilder) (address : Address) :
    BlockAccessListBuilder :=
  ensure_account b address

/-! ## Build phase -/

/-- Lexicographic byte-string order (Python `bytes` comparison). -/
def bytesLt : Bytes → Bytes → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as', b :: bs' =>
      if a.toNat < b.toNat then true
      else if a.toNat > b.toNat then false
      else bytesLt as' bs'

/-- `_build_from_builder(builder)`: sort every axis into the
    deterministic BAL (stable sorts, like Python `sorted`). -/
def _build_from_builder (b : BlockAccessListBuilder) : BlockAccessList :=
  let per_account := b.accounts.map (fun (address, ad) =>
    let storage_changes := (ad.storageChanges.map (fun (slot, slot_changes) =>
        SlotChanges.mk slot
          (slot_changes.mergeSort (fun x y => x.blockAccessIndex ≤ y.blockAccessIndex)))
      ).mergeSort (fun x y => x.slot ≤ y.slot)
    let storage_reads := (ad.storageReads.filter
        (fun slot => !dictHas ad.storageChanges slot)).mergeSort (· ≤ ·)
    { address := address
      storageChanges := storage_changes
      storageReads := storage_reads
      balanceChanges := ad.balanceChanges.mergeSort
        (fun x y => x.blockAccessIndex ≤ y.blockAccessIndex)
      nonceChanges := ad.nonceChanges.mergeSort
        (fun x y => x.blockAccessIndex ≤ y.blockAccessIndex)
      codeChanges := ad.codeChanges.mergeSort
        (fun x y => x.blockAccessIndex ≤ y.blockAccessIndex) })
  per_account.mergeSort (fun x y => !(bytesLt y.address x.address))

/-! ## Tx-diff extraction -/

/-- `_get_pre_tx_account(pre_tx_accounts, pre_state, address)` — falls
    back to the witness directly (no `reads` recording, but it DOES
    populate the Python storage-root cache → `recordPreStateRead`). -/
def _get_pre_tx_account (pre_tx_accounts : List (Address × Option Account))
    (address : Address) : TxM (Option Account) := do
  match dictGet? pre_tx_accounts address with
  | some acct => pure acct
  | none => do
      recordPreStateRead address
      let ts ← get
      StateT.lift (get_account_optional ts.parent.preState address)

/-- `_get_pre_tx_storage(pre_tx_storage, pre_state, address, key)`. -/
def _get_pre_tx_storage (pre_tx_storage : List (Address × List (Bytes32 × U256)))
    (address : Address) (key : Bytes32) : TxM U256 := do
  match (dictGet? pre_tx_storage address).bind (fun slots => dictGet? slots key) with
  | some v => pure v
  | none => do
      recordPreStateRead address
      let ts ← get
      StateT.lift (get_storage ts.parent.preState address key)

/-- `update_builder_from_tx(builder, tx_state)`: diff the transaction's
    writes against the block's cumulative state.  Must run BEFORE the
    merge (`incorporateTxIntoBlock` composes them). -/
def updateBuilderFromTx (builder : BlockAccessListBuilder) :
    TxM BlockAccessListBuilder := do
  let ts ← get
  let block_state := ts.parent
  let idx := builder.blockAccessIndex
  -- Account writes: balance / nonce / code changes.
  let mut b := builder
  for (address, post_account) in ts.accountWrites do
    let pre_account ← _get_pre_tx_account block_state.accountWrites address
    let pre_balance := (pre_account.map (·.balance)).getD 0
    let post_balance := (post_account.map (·.balance)).getD 0
    if pre_balance ≠ post_balance then
      b := add_balance_change b address idx post_balance
    let pre_nonce := (pre_account.map (·.nonce)).getD 0
    let post_nonce := (post_account.map (·.nonce)).getD 0
    if pre_nonce ≠ post_nonce then
      b := add_nonce_change b address idx post_nonce
    let pre_code_hash := (pre_account.map (·.codeHash)).getD EMPTY_CODE_HASH
    let post_code_hash := (post_account.map (·.codeHash)).getD EMPTY_CODE_HASH
    if pre_code_hash ≠ post_code_hash then
      let post_code ← getCode post_code_hash address
      b := add_code_change b address idx post_code
  -- Storage writes.
  for (address, slots) in ts.storageWrites do
    for (key, post_value) in slots do
      let pre_value ← _get_pre_tx_storage block_state.storageWrites address key
      if pre_value ≠ post_value then
        b := add_storage_write b address (bytesBEtoNat key) idx post_value
  pure b

/-- `incorporate_tx_into_block(tx_state, builder)` (`state_tracker.py`,
    function `incorporate_tx_into_block`): BAL update, then merge +
    clear. -/
def incorporateTxIntoBlock (builder : BlockAccessListBuilder) :
    TxM BlockAccessListBuilder := do
  let b ← updateBuilderFromTx builder
  mergeTxIntoBlock
  pure b

/-- `build_block_access_list(builder, block_state)`. -/
def build_block_access_list (builder : BlockAccessListBuilder)
    (block_state : BlockState) : BlockAccessList :=
  let b := block_state.storageReads.foldl (fun b (address, slot) =>
    add_storage_read b address (bytesBEtoNat slot)) builder
  let b := block_state.accountReads.foldl add_touched_account b
  _build_from_builder b

/-! ## Encoding / hashing -/

private def scalarB (n : Nat) : RLPItem := .bytes (EvmAsm.EL.RLP.Nat.toBytesBE n)

/-- `rlp.encode(block_access_list)`'s item (dataclasses as field
    lists, scalars minimal BE). -/
def balToRlpItem (bal : BlockAccessList) : RLPItem :=
  .list (bal.map (fun ac => .list
    [.bytes ac.address,
     .list (ac.storageChanges.map (fun sc => .list
       [scalarB sc.slot,
        .list (sc.changes.map (fun c => .list
          [scalarB c.blockAccessIndex, scalarB c.newValue]))])),
     .list (ac.storageReads.map scalarB),
     .list (ac.balanceChanges.map (fun c => .list
       [scalarB c.blockAccessIndex, scalarB c.postBalance])),
     .list (ac.nonceChanges.map (fun c => .list
       [scalarB c.blockAccessIndex, scalarB c.newNonce])),
     .list (ac.codeChanges.map (fun c => .list
       [scalarB c.blockAccessIndex, .bytes c.newCode]))]))

/-- `hash_block_access_list(block_access_list)`. -/
def hash_block_access_list (bal : BlockAccessList) : Hash32 :=
  keccak256 (EvmAsm.EL.RLP.encode (balToRlpItem bal))

/-- `GasCosts.BLOCK_ACCESS_LIST_ITEM` (`vm/gas.py`, class `GasCosts`). -/
def GasCosts.BLOCK_ACCESS_LIST_ITEM : Uint := 2000

/-- `validate_block_access_list_gas_limit(block_access_list,
    block_gas_limit)`. -/
def validate_block_access_list_gas_limit (bal : BlockAccessList)
    (block_gas_limit : Uint) : Except SpecError Unit := do
  let bal_items := bal.foldl (fun n account =>
    let unique_slots := (account.storageChanges.map (·.slot)).foldl setAdd []
    let unique_slots := account.storageReads.foldl setAdd unique_slots
    n + 1 + unique_slots.length) 0
  if bal_items > block_gas_limit / GasCosts.BLOCK_ACCESS_LIST_ITEM then
    throw (.invalidBlock "Block access list exceeds gas limit")

/-! ## Sanity checks

A full tracker→BAL→post-root scenario over the shared
`MptWriteVectors` two-account witness, cross-checked against the Python
spec at `bd8c673` (generator script in the PR description): read A,
move 10 wei A→B, write A's slot k3, bump A's nonce, snapshot, make two
writes that are then rolled back, read A's k1 through the rollback,
deploy code on B, incorporate, build + hash the BAL, and recompute the
post-state root from the extracted diff. -/

section
open MptWriteVectors

private def trackerScenario :
    Except SpecError (U256 × Nat × Nat × List Address) := do
  let ws : WitnessPreState :=
    { nodeDb := wNodeDb, stateRoot := wStateRoot, codeDb := [] }
  let m : TxM (U256 × BlockAccessListBuilder) := do
    let _ ← getAccount wAddrA
    moveEther wAddrA wAddrB 10
    setStorage wAddrA (k32 3) 9
    incrementNonce wAddrA
    let snap ← copyTxState
    setAccountBalance wAddrB 999
    setStorage wAddrA (k32 1) 0
    restoreTxState snap
    let v ← getStorage wAddrA (k32 1)
    setCode wAddrB [0x60, 0x00]
    let b ← incorporateTxIntoBlock { blockAccessIndex := 1 }
    pure (v, b)
  let ((v, b), ts) ← m.run { parent := { preState := ws } }
  let bal := build_block_access_list b ts.parent
  let diff := extract_block_diff ts.parent
  let cache₀ ← cacheFromReads ws ts.parent.preStateReads
  let root ← compute_state_root_and_trie_changes ws cache₀
    diff.accountChanges diff.storageChanges
  pure (v, bytesBEtoNat (hash_block_access_list bal), bytesBEtoNat root,
        ts.parent.preStateReads)

#guard
  match trackerScenario with
  | .ok (v, balHash, root, preReads) =>
      v == 0x2A
      && balHash == 0x4717683dc5dd0564e17998c463bf78dfbaf02a32c0a250abfda828a453786dc0
      && root == 0x07a2451914beaffffbf6939093ebab39d395799886dee3b53f8bca8d0e1354b8
      -- the witness-reaching reads are exactly A and B
      && preReads.length == 2 && preReads.contains wAddrA && preReads.contains wAddrB
  | .error _ => false

-- Transient storage: set, read back, zero-pop, survives nothing.
#guard
  match (do
    let m : TxM (U256 × U256) := do
      setTransientStorage wAddrA (k32 1) 5
      let a ← getTransientStorage wAddrA (k32 1)
      setTransientStorage wAddrA (k32 1) 0
      let b ← getTransientStorage wAddrA (k32 1)
      pure (a, b)
    m.run { parent := { preState :=
      { nodeDb := wNodeDb, stateRoot := wStateRoot, codeDb := [] } } } :
      Except SpecError ((U256 × U256) × TransactionState)) with
  | .ok ((5, 0), _) => true | _ => false

end

end EvmAsm.Stateless.SpecRef
