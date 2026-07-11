/-
  EvmAsm.Stateless.SpecRef.WitnessState

  Port of the four module-level functions in
  `execution-specs/src/ethereum/forks/amsterdam/witness_state.py`
  (`@tests-zkevm@v0.4.0`):

  * `build_node_db`            (`witness_state.py:36`)
  * `build_code_db`            (`witness_state.py:44`)
  * `_trie_lookup`             (`witness_state.py:52`)
  * `_decode_account_from_leaf`(`witness_state.py:102`)

  The `WitnessState` *methods* (`get_account_optional`, `get_storage`,
  `get_code`, `compute_state_root_and_trie_changes`, …) are the read/write
  side of the `PreState` protocol consumed by block execution; they sit
  BEHIND the execution seam (see `Stateless.lean`) and are out of scope
  here. Likewise `decode_witness_to_mpt` (which turns a node DB into the
  `MutableNode` tree `_trie_lookup` walks) lives in `incremental_mpt.py`,
  not among the four target functions — so `_trie_lookup` is ported as a
  pure walk over an already-decoded `MutableNode`, and the `#guard`s below
  exercise it on hand-built trees. (`decode_witness_to_mpt` is now ported
  in `IncrementalMpt.lean` — bead `s1d19.1`, obligation #7 — which reuses
  the `MutableNode` type defined below.)
-/

import EvmAsm.Stateless.SpecRef.Types
import EvmAsm.EL.RLP.FullDecode

namespace EvmAsm.Stateless.SpecRef

open EvmAsm.EL.RLP (RLPItem decodeFully)

/-! ## Empty-trie / empty-code sentinels (`ethereum.state`, `merkle_patricia_trie`) -/

/-- `EMPTY_CODE_HASH = keccak256(b"")`. -/
def EMPTY_CODE_HASH : Hash32 := keccak256 []

/-- `EMPTY_TRIE_ROOT = keccak256(rlp.encode(b"")) = keccak256(0x80)`. -/
def EMPTY_TRIE_ROOT : Root := keccak256 [0x80]

-- keccak256("") = c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
#guard bytesBEtoNat EMPTY_CODE_HASH
  = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
-- EMPTY_TRIE_ROOT = keccak256(0x80), matching merkle_patricia_trie.py:63
#guard bytesBEtoNat EMPTY_TRIE_ROOT
  = 0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421

/-! ## `build_node_db` / `build_code_db` (`witness_state.py:36`, `:44`)

Python builds a `Dict[keccak256(entry), entry]`; we model the DB as an
association list `List (Hash32 × Bytes)` in witness order. -/

/-- Build the `hash → RLP` mapping from witness state preimages. -/
def build_node_db (state_entries : List Bytes) : List (Hash32 × Bytes) :=
  state_entries.map (fun entry => (keccak256 entry, entry))

/-- Build the `code_hash → bytecode` mapping from witness codes. -/
def build_code_db (code_entries : List Bytes) : List (Hash32 × Bytes) :=
  code_entries.map (fun code => (keccak256 code, code))

/-! ## MPT node model (`incremental_mpt.MutableNode`)

The `MutableNode` union `_trie_lookup` walks. Nibble sequences
(`rest_of_key`, `key_segment`, and the key path) are `Bytes` with each byte
holding a single nibble value `0..15`, matching the Python
`bytearray` of nibbles. A branch has 16 children (`none` for absent) and a
value (`empty` = absent). `hashed` is an unresolved node. -/
inductive MutableNode where
  | hashed (hash : Bytes)
  | leaf (restOfKey : Bytes) (value : Bytes)
  | extension (keySegment : Bytes) (child : MutableNode)
  | branch (children : List (Option MutableNode)) (value : Bytes)
  deriving Inhabited

/-! ## `_trie_lookup` (`witness_state.py:52`) -/

/-- Expand a byte string into its nibble sequence (`byte >> 4`, `byte & 0x0F`). -/
def keyToNibbles (key : Bytes) : Bytes :=
  key.flatMap (fun b =>
    [BitVec.ofNat 8 (b.toNat >>> 4), BitVec.ofNat 8 (b.toNat &&& 0x0F)])

/-- Walk a decoded MPT from `node`, following `nibbles` from position `pos`.
    Returns the leaf value or `none` if not found; errors on an unresolved
    `HashedNode`. Fuel bounds the nibble path length. -/
def trieLookupAux : Nat → Option MutableNode → Bytes → Nat → Except SpecError (Option Bytes)
  | _, none, _, _ => .ok none
  | 0, _, _, _ => .ok none
  | f + 1, some node, nibbles, pos =>
    match node with
    | .hashed _ => .error .unresolvedHashedNode
    | .leaf restOfKey value =>
        if nibbles.drop pos == restOfKey then .ok (some value) else .ok none
    | .extension keySegment child =>
        if (nibbles.drop pos).take keySegment.length == keySegment then
          trieLookupAux f (some child) nibbles (pos + keySegment.length)
        else .ok none
    | .branch children value =>
        if nibbles.length ≤ pos then
          .ok (if value.isEmpty then none else some value)
        else
          let idx := (nibbles.getD pos 0).toNat
          trieLookupAux f (children.getD idx none) nibbles (pos + 1)

/-- `_trie_lookup(root_node, key_hash)`. `root` is `Option` to capture the
    empty-trie (`None` root) case the Python `while node is not None` guard
    handles. -/
def trieLookup (root : Option MutableNode) (keyHash : Hash32) :
    Except SpecError (Option Bytes) :=
  let nibbles := keyToNibbles keyHash
  trieLookupAux (nibbles.length + 2) root nibbles 0

/-! ## `_decode_account_from_leaf` (`witness_state.py:102`) -/

/-- Decode `(nonce, balance, storage_root, code_hash)` from a trie leaf.
    Returns the `Account` and the `storage_root` separately (mirrors the
    Python tuple return). -/
def decode_account_from_leaf (leaf_value : Bytes) :
    Except SpecError (Account × Root) := do
  match decodeFully leaf_value with
  | some (.list [.bytes n, .bytes b, .bytes sr, .bytes ch]) =>
      let nonce : Uint := if n.isEmpty then 0 else bytesBEtoNat n
      let balance : U256 := if b.isEmpty then 0 else bytesBEtoNat b
      let storageRoot : Root := if sr.isEmpty then EMPTY_TRIE_ROOT else sr
      let codeHash : Hash32 := if ch.isEmpty then EMPTY_CODE_HASH else ch
      pure ({ nonce, balance, codeHash }, storageRoot)
  | _ => .error .accountLeafMalformed

/-! ## Sanity checks -/

-- build_node_db keys are the keccak256 of the entries.
#guard (build_node_db [[0x80]]).map (fun p => bytesBEtoNat p.1)
  == [0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421]

-- A single-leaf trie whose leaf key is all the nibbles of key `0xAB` returns
-- its value; a mismatching key returns none.
#guard
  let key : Bytes := [0xAB]
  let nibbles := keyToNibbles key   -- [0x0A, 0x0B]
  match trieLookup (some (.leaf nibbles [0x99])) key with
  | .ok (some [0x99]) => true | _ => false

#guard
  match trieLookup (some (.leaf [0x0C, 0x0D] [0x99])) [0xAB] with
  | .ok none => true | _ => false

-- Empty (None) root → not found.
#guard match trieLookup none [0xAB] with | .ok none => true | _ => false

-- Unresolved HashedNode → error.
#guard
  match trieLookup (some (.hashed [])) [0xAB] with
  | .error .unresolvedHashedNode => true | _ => false

-- A branch dispatching on the first nibble (0x0A) of key 0xAB to a leaf.
#guard
  let leaf : MutableNode := .leaf [0x0B] [0x77]
  let children : List (Option MutableNode) :=
    (List.range 16).map (fun i => if i == 0x0A then some leaf else none)
  match trieLookup (some (.branch children [])) [0xAB] with
  | .ok (some [0x77]) => true | _ => false

-- Decode a minimal account leaf: rlp([nonce=1, balance=0x0de0b6b3a7640000,
-- storage_root=EMPTY_TRIE_ROOT, code_hash=EMPTY_CODE_HASH]).
#guard
  let leaf : RLPItem := .list
    [.bytes [0x01],
     .bytes (natToBytesBE 8 1000000000000000000),
     .bytes EMPTY_TRIE_ROOT,
     .bytes EMPTY_CODE_HASH]
  (decode_account_from_leaf (EvmAsm.EL.RLP.encode leaf)).toOption
    == some ({ nonce := 1, balance := 1000000000000000000, codeHash := EMPTY_CODE_HASH },
             EMPTY_TRIE_ROOT)

-- Empty scalar fields default to 0 / empty sentinels.
#guard
  let leaf : RLPItem := .list [.bytes [], .bytes [], .bytes [], .bytes []]
  (decode_account_from_leaf (EvmAsm.EL.RLP.encode leaf)).toOption
    == some ({ nonce := 0, balance := 0, codeHash := EMPTY_CODE_HASH }, EMPTY_TRIE_ROOT)

end EvmAsm.Stateless.SpecRef
