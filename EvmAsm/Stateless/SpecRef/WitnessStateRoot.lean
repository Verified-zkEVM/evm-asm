/-
  EvmAsm.Stateless.SpecRef.WitnessStateRoot

  Port of `WitnessState.compute_state_root_and_trie_changes` in
  `execution-specs/src/ethereum/forks/amsterdam/witness_state.py`
  (`@tests-zkevm@v0.5.0`, `bd8c673`, method
  `compute_state_root_and_trie_changes`) — the post-state-root
  computation, obligation #8 (bead `evm-asm-s1d19.4`), including the
  v0.5.0 `storage_clears` parameter.

  ## Modeling notes

  * **The `_storage_root_cache` is observable here** (unlike on the read
    surface, see `WitnessReads.lean`): the `get_storage_root` closure for
    the `account_changes` pass reads
    `self._storage_root_cache.get(addr, EMPTY_TRIE_ROOT)` *without*
    populating it, so its result depends on which addresses were read —
    by block execution before this call, and by this method's own
    `get_account_optional` calls.  The port therefore threads the cache
    explicitly: `cache₀` is the cache content at entry (every address
    `get_account_optional` was called on during execution, mapped to its
    storage root), and the two internal passes extend it exactly where
    Python does.
  * **Iteration order**: Python iterates `storage_changes` /
    `account_changes` dicts in insertion order — mirrored by the assoc
    lists — and `storage_touched = set(storage_changes) |
    set(storage_clears)` in *unspecified* set order; every operation in
    that pass is an insert/update of a distinct state-trie key (never a
    delete), and distinct-key MPT inserts commute (same resulting tree,
    and `HashedNode` contact depends only on each key's own path), so
    the choice `storage_changes ++ (storage_clears \ storage_changes)`
    is observationally equal.
  * Python returns `(root, [])` — the `List[InternalNode]` component is
    always empty at `bd8c673` — so the port returns only the root.
-/

import EvmAsm.Stateless.SpecRef.IncrementalMptWrite
import EvmAsm.Stateless.SpecRef.WitnessReads

namespace EvmAsm.Stateless.SpecRef

/-- The `_storage_root_cache` content, threaded explicitly (see header). -/
abbrev StorageRootCache := List (Address × Root)

/-- `self._storage_root_cache.get(address, EMPTY_TRIE_ROOT)`. -/
def cacheGet (cache : StorageRootCache) (address : Address) : Root :=
  ((cache.find? (·.1 == address)).map (·.2)).getD EMPTY_TRIE_ROOT

/-- `address in self._storage_root_cache`. -/
def cacheHas (cache : StorageRootCache) (address : Address) : Bool :=
  cache.any (·.1 == address)

/-- `get_account_optional`'s cache write (`WitnessReads.lean` models the
    read surface cache-free; here the fill is observable):
    `self._storage_root_cache[address] = storage_root-or-EMPTY_TRIE_ROOT`. -/
def cacheFill (ws : WitnessPreState) (cache : StorageRootCache)
    (address : Address) : Except SpecError StorageRootCache := do
  let sr ← _storage_root_of ws address
  if cacheHas cache address then
    pure (cache.map (fun p => if p.1 == address then (address, sr) else p))
  else
    pure (cache ++ [(address, sr)])

/-- Reconstruct the `_storage_root_cache` content at block end from the
    set of witness-reaching read addresses (`BlockState.preStateReads`):
    the values are the deterministic `_storage_root_of` results. -/
def cacheFromReads (ws : WitnessPreState) (reads : List Address) :
    Except SpecError StorageRootCache :=
  reads.foldlM (cacheFill ws) []

/-- `compute_state_root_and_trie_changes(account_changes, storage_changes,
    storage_clears)`.  `cache₀`: the `_storage_root_cache` at entry (see
    header).  Values: `account_changes` uses `none` for deleted accounts
    (`Optional[Account]`), `storage_changes` slots use `0` for cleared
    slots. -/
def compute_state_root_and_trie_changes (ws : WitnessPreState)
    (cache₀ : StorageRootCache)
    (account_changes : List (Address × Option Account))
    (storage_changes : List (Address × List (Bytes32 × U256)))
    (storage_clears : List Address := []) : Except SpecError Root := do
  -- Pass 1: per-address storage tries → new storage roots.
  let mut cache := cache₀
  let mut new_storage_roots : List (Address × Root) := []
  for (address, slots) in storage_changes do
    if !(storage_clears.any (· == address)) && !(cacheHas cache address) then
      cache ← cacheFill ws cache address
    let old_root :=
      if storage_clears.any (· == address) then EMPTY_TRIE_ROOT
      else cacheGet cache address
    let mut storage_mpt ← decode_witness_mpt ws.nodeDb old_root true (some (.u256 0))
    -- Insertions + updates before deletions, to minimize branch compressions.
    for (key, value) in slots do
      if value != 0 then
        storage_mpt ← mpt_set storage_mpt key (some (.u256 value))
    for (key, value) in slots do
      if value == 0 then
        storage_mpt ← mpt_set storage_mpt key (some (.u256 0))
    new_storage_roots := new_storage_roots ++ [(address, ← mpt_root storage_mpt)]

  -- The state trie from the witness.
  let mut state_mpt ← decode_witness_mpt ws.nodeDb ws.stateRoot true none

  -- Pass 2: storage-touched addresses absent from account_changes keep
  -- their account but pick up the new storage root.
  let storage_touched :=
    storage_changes.map (·.1)
      ++ storage_clears.filter (fun a => !(storage_changes.any (·.1 == a)))
  for address in storage_touched do
    if !(account_changes.any (·.1 == address)) then
      let account ← get_account_optional ws address
      cache ← cacheFill ws cache address
      if let some a := account then
        let sr := ((new_storage_roots.find? (·.1 == address)).map (·.2)).getD
          EMPTY_TRIE_ROOT
        state_mpt ← mpt_set state_mpt address (some (.account a))
          (get_storage_root := some (fun _ => sr))

  -- Pass 3: account changes, with the storage-root closure over the
  -- final cache.
  let cacheFinal := cache
  let get_storage_root : Address → Root := fun addr =>
    match new_storage_roots.find? (·.1 == addr) with
    | some p => p.2
    | none =>
        if storage_clears.any (· == addr) then EMPTY_TRIE_ROOT
        else cacheGet cacheFinal addr
  for (address, account) in account_changes do
    state_mpt ← mpt_set state_mpt address (account.map .account)
      (get_storage_root := some get_storage_root)

  mpt_root state_mpt

/-! ## Sanity checks

End-to-end over the shared `MptWriteVectors` witness (two accounts,
`0xA1…` with a two-slot storage trie); every expected root is
cross-checked against the Python `WitnessState` at `bd8c673`. -/

section
open MptWriteVectors

private def testWs' : WitnessPreState :=
  { nodeDb := wNodeDb, stateRoot := wStateRoot, codeDb := [] }

-- Execution read A and B (cache filled for both); B's balance changes,
-- D is created, A clears one slot and writes another.
#guard
  (compute_state_root_and_trie_changes testWs'
    (cache₀ := [(wAddrA, srootA), (wAddrB, EMPTY_TRIE_ROOT)])
    (account_changes := [(wAddrB, some { acctB with balance := 6 }),
                         (wAddrD, some acctD)])
    (storage_changes := [(wAddrA, [(k32 1, 0), (k32 3, 9)])])).toOption.map bytesBEtoNat
  == some 0x062aba06a58d8c131a312254525a767a623e65635b65014353a122b4a02c475a

-- storage_clears: A's storage is rebuilt from the empty trie (old slots
-- gone), then k3 written.
#guard
  (compute_state_root_and_trie_changes testWs'
    (cache₀ := [(wAddrA, srootA)])
    (account_changes := [])
    (storage_changes := [(wAddrA, [(k32 3, 9)])])
    (storage_clears := [wAddrA])).toOption.map bytesBEtoNat
  == some 0xea7cba513b3ff34d17534862573077aa3427b41df241d1f081fce6d14ece5f56

-- Account deletion (branch collapse onto the remaining account leaf),
-- with an empty entry cache (no reads during execution).
#guard
  (compute_state_root_and_trie_changes testWs' (cache₀ := [])
    (account_changes := [(wAddrB, none)])
    (storage_changes := [])).toOption.map bytesBEtoNat
  == some 0x45fa6823f441f19afb852972d0c225cacbcee853c7e9ea979cde53cae8bfb38c

-- No changes at all: the root is unchanged.
#guard
  (compute_state_root_and_trie_changes testWs' (cache₀ := [])
    (account_changes := []) (storage_changes := [])).toOption
  == some wStateRoot

end

end EvmAsm.Stateless.SpecRef
