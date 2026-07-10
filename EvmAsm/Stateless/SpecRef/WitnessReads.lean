/-
  EvmAsm.Stateless.SpecRef.WitnessReads

  Port of the `WitnessState` read methods in
  `execution-specs/src/ethereum/forks/amsterdam/witness_state.py`
  (`@tests-zkevm@v0.5.0`, `bd8c673`):

  * `_get_decoded_secure_root` (method `_get_decoded_secure_root`)
  * `get_account_optional`     (method `get_account_optional`)
  * `get_storage`              (method `get_storage`)
  * `get_code`                 (method `get_code`)
  * `account_has_storage`      (method `account_has_storage`)

  These are the authenticated witness-backed reads of the `PreState`
  protocol (bead `evm-asm-s1d19.2`; scope:
  docs/agents/specref-execution-seam-scope.md §6).  They compose the
  `s1d19.1` witness decoder (`decode_witness_to_mpt`, obligation #7) with
  `trieLookup` / `decode_account_from_leaf` from `WitnessState.lean`.
  `compute_state_root_and_trie_changes` (the write side) is bead `s1d19.4`.

  ## Modeling note: caches as recomputation

  The Python `WitnessState` dataclass carries two mutable memo caches:

  * `_decoded_secure_roots : Dict[Root, MutableNode]` — memoizes
    `decode_witness_to_mpt(self._node_db, root_hash, secured=True)`;
  * `_storage_root_cache : Dict[Address, Root]` — populated by every
    `get_account_optional` call with the account's `storage_root`
    (`EMPTY_TRIE_ROOT` for a missing account), and read back by
    `get_storage` / `account_has_storage`, each of which first calls
    `get_account_optional` on a cache miss.

  Both memoize total deterministic functions of the immutable fields
  (`_node_db`, `_state_root`): the decoded root of a given hash never
  changes, and the storage root of a given address is always the result of
  the same state-trie lookup.  On the read-only surface ported here, every
  cache hit therefore returns exactly what recomputation returns — same
  values, same raised exceptions (a lookup that would raise on recompute
  raised at cache-fill time and never populated the cache).  We model the
  reads cache-free (`_storage_root_of` recomputes what `get_storage` /
  `account_has_storage` would read from `_storage_root_cache`), which is
  observationally equal.  The one place the cache IS observable —
  `compute_state_root_and_trie_changes`'s `get_storage_root` closure reads
  `_storage_root_cache.get(addr, EMPTY_TRIE_ROOT)` *without* populating it,
  so its result depends on which reads ran before — is out of scope here
  and is handled by `s1d19.4` (the write side threads the set of read
  addresses explicitly).
-/

import EvmAsm.Stateless.SpecRef.IncrementalMpt

namespace EvmAsm.Stateless.SpecRef

open EvmAsm.EL.RLP (RLPItem decodeFully)

/-! ## The witness-backed pre-state

The immutable fields of the Python `WitnessState` dataclass
(`witness_state.py`, class `WitnessState`): `_node_db`, `_state_root`,
`_code_db`.  The two memo caches are not modeled (see the header). -/

/-- Witness-backed pre-state passed to execution (`WitnessState.__init__`). -/
structure WitnessPreState where
  nodeDb : List (Hash32 × Bytes)
  stateRoot : Root
  codeDb : List (Hash32 × Bytes)
  deriving Repr

/-! ## `_get_decoded_secure_root` (`witness_state.py`, method `_get_decoded_secure_root`) -/

/-- Decode a secured trie root for read-only lookups.  The Python method is
    `decode_witness_to_mpt` behind the `_decoded_secure_roots` memo cache
    plus an `EMPTY_TRIE_ROOT → None` shortcut; `decode_witness_to_mpt`
    already implements that shortcut, so cache-free this is exactly it. -/
def _get_decoded_secure_root (ws : WitnessPreState) (root_hash : Root) :
    Except SpecError (Option MutableNode) :=
  decode_witness_to_mpt ws.nodeDb root_hash

/-! ## `get_account_optional` (`witness_state.py`, method `get_account_optional`) -/

/-- The state-trie leaf for an address (`keccak256(address)` secure key),
    shared by the account read and the storage-root recomputation. -/
private def accountLeaf (ws : WitnessPreState) (address : Address) :
    Except SpecError (Option Bytes) := do
  trieLookup (← _get_decoded_secure_root ws ws.stateRoot) (keccak256 address)

/-- Get the account at an address; `none` if absent.  (The Python method
    also fills `_storage_root_cache[address]` — memoization only, see the
    header note.) -/
def get_account_optional (ws : WitnessPreState) (address : Address) :
    Except SpecError (Option Account) := do
  match ← accountLeaf ws address with
  | none => pure none
  | some leaf => pure (some (← decode_account_from_leaf leaf).1)

/-- What `_storage_root_cache[address]` holds after `get_account_optional`:
    the account leaf's `storage_root`, or `EMPTY_TRIE_ROOT` for a missing
    account. -/
def _storage_root_of (ws : WitnessPreState) (address : Address) :
    Except SpecError Root := do
  match ← accountLeaf ws address with
  | none => pure EMPTY_TRIE_ROOT
  | some leaf => pure (← decode_account_from_leaf leaf).2

/-! ## `get_storage` (`witness_state.py`, method `get_storage`) -/

/-- Get a storage value; `0` if the key has not been set.  The storage-trie
    leaf is the RLP encoding of the (non-zero) `U256` value; a decoded
    RLP *list* falls through to `U256(0)` in Python (`isinstance` check),
    a `DecodingError` propagates → rejection. -/
def get_storage (ws : WitnessPreState) (address : Address) (key : Bytes32) :
    Except SpecError U256 := do
  let storage_root ← _storage_root_of ws address
  if storage_root == EMPTY_TRIE_ROOT then
    pure 0
  else
    match ← trieLookup (← _get_decoded_secure_root ws storage_root) (keccak256 key) with
    | none => pure 0
    | some leaf =>
        match decodeFully leaf with
        | some (.bytes b) => pure (if b.isEmpty then 0 else bytesBEtoNat b)
        | some (.list _) => pure 0
        | none => throw .storageLeafMalformed

/-! ## `get_code` (`witness_state.py`, method `get_code`) -/

/-- Get the bytecode for a code hash: `b""` for `EMPTY_CODE_HASH`, else
    `self._code_db[code_hash]` (`KeyError` → rejection).  Same dict-as-
    assoc-list convention as `nodeDbLookup` (keccak-keyed, duplicates
    identical). -/
def get_code (ws : WitnessPreState) (code_hash : Hash32) :
    Except SpecError Bytes :=
  if code_hash == EMPTY_CODE_HASH then
    pure []
  else
    match (ws.codeDb.find? (fun p => p.1 == code_hash)).map (·.2) with
    | some code => pure code
    | none => throw .codeHashMissing

/-! ## `account_has_storage` (`witness_state.py`, method `account_has_storage`) -/

/-- Whether an account has any storage (EIP-7610): its storage root is not
    `EMPTY_TRIE_ROOT`. -/
def account_has_storage (ws : WitnessPreState) (address : Address) :
    Except SpecError Bool := do
  pure ((← _storage_root_of ws address) != EMPTY_TRIE_ROOT)

/-! ## Sanity checks

A hand-assembled two-account witness, read end-to-end through the
keccak-keyed node DB: `addrA` has code and one storage slot, `addrB` is
codeless/storageless with a bare balance.  Single-leaf tries: the leaf's
`rest_of_key` is the full 64-nibble secure key, whose compact encoding is
`0x20 :: keccak256(key)` (even leaf). -/

private def enc' (i : RLPItem) : Bytes := EvmAsm.EL.RLP.encode i

private def addrA : Address := List.replicate 20 0xA1
private def addrB : Address := List.replicate 20 0x00
private def addrC : Address := List.replicate 20 0xC3   -- absent
private def slotKey : Bytes32 := List.replicate 32 0x01
private def codeA : Bytes := [0x60, 0x00, 0x60, 0x00, 0xF3]

-- addrA's storage trie: single leaf keccak(slotKey) → rlp(0x2A).
private def storageLeafA : Bytes :=
  enc' (.list [.bytes (0x20 :: keccak256 slotKey), .bytes (enc' (.bytes [0x2A]))])

-- addrA's account body: [nonce=1, balance=100, storage_root, code_hash].
private def acctBodyA : Bytes :=
  enc' (.list [.bytes [0x01], .bytes [0x64],
    .bytes (keccak256 storageLeafA), .bytes (keccak256 codeA)])

-- addrB's account body: bare balance, no code, no storage.
private def acctBodyB : Bytes :=
  enc' (.list [.bytes [], .bytes [0x05], .bytes [], .bytes []])

-- The two-account state trie branches on the first nibble of the secure
-- keys (keccak(addrA) starts 0x8…, keccak(addrB) starts 0x5…).
private def nibblesOf (b : Bytes) : Bytes := keyToNibbles b
private def secA := keccak256 addrA
private def secB := keccak256 addrB

-- Guard-time check that the two secure keys really split at nibble 0.
#guard (nibblesOf secA).getD 0 0 != (nibblesOf secB).getD 0 0

-- Inline leaves under the branch: rest_of_key drops the first nibble
-- (odd length 63 → compact prefix 0x3_ carrying the second nibble).
private def leafUnderBranch (sec : Bytes) (body : Bytes) : RLPItem :=
  let nibs := (nibblesOf sec).drop 1
  let compact : Bytes :=
    (BitVec.ofNat 8 (0x30 + (nibs.getD 0 0).toNat)) ::
      (List.range 31).map (fun i =>
        BitVec.ofNat 8 (((nibs.getD (2*i+1) 0).toNat <<< 4) + (nibs.getD (2*i+2) 0).toNat))
  .list [.bytes compact, .bytes body]

private def stateRootNode : Bytes :=
  enc' (.list ((List.range 16).map (fun i =>
    if i == ((nibblesOf secA).getD 0 0).toNat then leafUnderBranch secA acctBodyA
    else if i == ((nibblesOf secB).getD 0 0).toNat then leafUnderBranch secB acctBodyB
    else .bytes []) ++ [.bytes []]))

private def testWs : WitnessPreState :=
  { nodeDb := build_node_db [stateRootNode, storageLeafA]
    stateRoot := keccak256 stateRootNode
    codeDb := build_code_db [codeA] }

-- get_account_optional: present accounts decode; absent address is none.
#guard (get_account_optional testWs addrA).toOption
  == some (some { nonce := 1, balance := 100, codeHash := keccak256 codeA })
#guard (get_account_optional testWs addrB).toOption
  == some (some { nonce := 0, balance := 5, codeHash := EMPTY_CODE_HASH })
#guard (get_account_optional testWs addrC).toOption == some none

-- get_storage: set slot reads back; unset slot and storageless/absent
-- accounts read 0.
#guard (get_storage testWs addrA slotKey).toOption == some 0x2A
#guard (get_storage testWs addrA (List.replicate 32 0x02)).toOption == some 0
#guard (get_storage testWs addrB slotKey).toOption == some 0
#guard (get_storage testWs addrC slotKey).toOption == some 0

-- account_has_storage (EIP-7610): only addrA.
#guard (account_has_storage testWs addrA).toOption == some true
#guard (account_has_storage testWs addrB).toOption == some false
#guard (account_has_storage testWs addrC).toOption == some false

-- get_code: EMPTY_CODE_HASH → empty without consulting the DB; a present
-- hash reads back; a missing hash is a KeyError → rejection.
#guard (get_code testWs EMPTY_CODE_HASH).toOption == some []
#guard (get_code testWs (keccak256 codeA)).toOption == some codeA
#guard match get_code testWs (List.replicate 32 0x33) with
  | .error .codeHashMissing => true | _ => false

-- Withheld storage node: decoding addrA's account succeeds, but reading
-- the (hash-referenced) storage slot hits the missing root → rejection,
-- never a wrong value.
#guard
  let wsWithheld : WitnessPreState :=
    { testWs with nodeDb := build_node_db [stateRootNode] }
  match get_storage wsWithheld addrA slotKey with
  | .error .witnessRootMissing => true | _ => false

end EvmAsm.Stateless.SpecRef
