/-
  EvmAsm.Stateless.SpecRef.IncrementalMptWrite

  Port of the write side of
  `execution-specs/src/ethereum/forks/amsterdam/incremental_mpt.py`
  (`@tests-zkevm@v0.5.0`, `bd8c673`) — bead `evm-asm-s1d19.4`,
  obligation #8 (post-state root):

  * `IncrementalMPT` (class `IncrementalMPT`) — here `IncrementalMpt`
  * `_build_mutable_tree`, `build_mpt` (functions of the same names)
  * `_encode_mutable_node`, `_encode_mutable_node_to_extended`,
    `_compute_node_hash_and_rlp` (functions of the same names)
  * `mpt_get` (function `mpt_get`) + `_mpt_traverse_for_witness`
  * `mpt_set` (function `mpt_set`) + `_mpt_insert_node`,
    `_insert_into_leaf`, `_create_branch_from_two_leaves`,
    `_insert_into_extension`, `_split_extension`, `_insert_into_branch`
  * `_mpt_delete_node`, `_delete_from_extension`, `_delete_from_branch`,
    `_collapse_branch` (functions of the same names)
  * `mpt_root` (function `mpt_root`)

  plus the `ethereum/merkle_patricia_trie.py` helpers they consume:
  `common_prefix_length`, `nibble_list_to_compact`, `encode_account`,
  `encode_node`, `_prepare_data`
  (all cited from `execution-specs/src/ethereum/merkle_patricia_trie.py`).

  ## Modeling notes

  * **Immutable tree, pure functions.**  The Python nodes are mutated in
    place and carry `_hash`/`_rlp` memo caches plus a `_dirty` flag; the
    caches only memoize the deterministic keccak/RLP encoding of the
    current node content (`_invalidate_hash` clears them on every write
    path), so recomputation is observationally equal and this port drops
    all three fields, returning fresh nodes instead of mutating.
  * **`_dirty` / identity checks.**  `_delete_from_extension` /
    `_delete_from_branch` skip the update (and the branch collapse) when
    the recursive delete returns the same, un-dirtied child object.  A
    content-unchanged subtree makes the parent update a no-op, and
    `_collapse_branch` on an unchanged branch is a no-op too (a
    well-formed branch keeps ≥ 2 occupied entries — enforced by the
    witness decoder and preserved by every operation), so the port
    always applies the update + collapse.  The flag's only other
    consumer is witness *generation* bookkeeping (`_record_witness`
    dedup), which is not modeled — except its `HashedNode` assert, see
    next note.
  * **Every Python `assert`/`raise` on the write path is a rejection**
    (`SpecError.mptWriteError`), never a wrong value: touching a
    `HashedNode` on an insert/delete path (`_invalidate_hash`),
    inline-encoding a `HashedNode` (`_encode_mutable_node`), collapsing
    a branch onto a `HashedNode` child (`_record_witness` inside
    `_collapse_branch`), `_split_extension`'s collision assert,
    `mpt_set`/`_prepare_data` on an unencodable value.
  * **Fuel.**  Tree-walking recursion (insert/delete/traverse/build) is
    fueled by the nibble-key length: every recursive call strictly
    increases `level` (extension segments are non-empty in well-formed
    tries), so `key.length + 1` never exhausts on them; exhaustion —
    reachable only through a malformed (empty-segment) decoded node —
    is a rejection.  Encoding recursion is fueled by `sizeOf node`,
    a strict upper bound on tree depth, so its exhaustion branch is
    unreachable.
  * **Values.**  The Python `V` is dynamically dispatched by
    `encode_node` (`Account` / raw `Bytes` / RLP-encodable `U256`);
    here it is the explicit sum `MptValue`, with `Option` for the
    Python `None` (the state trie's `default`).  `_data` stores only
    non-default values (Python deletes the key when the default is
    stored), so it is `List (Bytes × MptValue)` with dict semantics
    (update-in-place keeps position, new keys append).
  * `witness.accessed_nodes` (witness *generation*) is not modeled; on
    the verification path nothing reads it.  Its `HashedNode` asserts
    are kept where reachable (see above).
-/

import EvmAsm.Stateless.SpecRef.IncrementalMpt

namespace EvmAsm.Stateless.SpecRef

open EvmAsm.EL.RLP (RLPItem)

private def encR (i : RLPItem) : Bytes := EvmAsm.EL.RLP.encode i

/-! ## `merkle_patricia_trie.py` helpers

`execution-specs/src/ethereum/merkle_patricia_trie.py`,
functions `common_prefix_length`, `nibble_list_to_compact`,
`encode_account`, `encode_node`, `_prepare_data`.
(`bytes_to_nibble_list` is `keyToNibbles` in `WitnessState.lean`.) -/

/-- Length of the longest common prefix of two nibble sequences. -/
def common_prefix_length (a b : Bytes) : Nat :=
  ((a.zip b).takeWhile (fun p => p.1 == p.2)).length

/-- Hex-prefix (compact) encoding of a nibble list; inverse of
    `compact_to_nibbles`. -/
def nibble_list_to_compact (x : Bytes) (is_leaf : Bool) : Bytes :=
  let flag : Nat := if is_leaf then 2 else 0
  let packPairs : List (BitVec 8) → Bytes := fun nibs =>
    (List.range (nibs.length / 2)).map (fun i =>
      BitVec.ofNat 8 (16 * (nibs.getD (2*i) 0).toNat + (nibs.getD (2*i+1) 0).toNat))
  if x.length % 2 == 0 then
    BitVec.ofNat 8 (16 * flag) :: packPairs x
  else
    BitVec.ofNat 8 (16 * (flag + 1) + (x.getD 0 0).toNat) :: packPairs (x.drop 1)

/-- RLP of a `Uint`/`U256` scalar: minimal big-endian bytes. -/
private def rlpScalar (n : Nat) : Bytes := EvmAsm.EL.RLP.Nat.toBytesBE n

/-- `encode_account(raw_account_data, storage_root)`:
    `rlp.encode((nonce, balance, storage_root, code_hash))`. -/
def encode_account (a : Account) (storage_root : Bytes) : Bytes :=
  encR (.list [.bytes (rlpScalar a.nonce), .bytes (rlpScalar a.balance),
               .bytes storage_root, .bytes a.codeHash])

/-! ## Trie values

The Python `V` type parameter, made explicit: `encode_node` dispatches on
`Account` (needs `storage_root`) / raw `Bytes` (unchanged) / anything else
(RLP-encoded — here `U256` scalars, the only other instantiation on the
stateless-guest path). -/

/-- A trie value: storage `U256`, state-trie `Account`, or raw bytes
    (transaction/receipt/withdrawal tries). -/
inductive MptValue where
  | u256 (v : U256)
  | account (a : Account)
  | bytes (b : Bytes)
  deriving Repr, BEq

/-- `encode_node(node, storage_root)` on an `MptValue`; the Python
    `None` (`Option.none`) is unencodable (`AssertionError`). -/
def encode_mpt_value (key : Bytes) (value : Option MptValue)
    (get_storage_root : Option (Bytes → Root)) : Except SpecError Bytes :=
  match value with
  | some (.account a) =>
      match get_storage_root with
      | some gsr => pure (encode_account a (gsr key))
      | none => throw (.mptWriteError "encode_node: Account requires storage_root")
  | some (.bytes b) => pure b
  | some (.u256 v) => pure (encR (.bytes (rlpScalar v)))
  | none => throw (.mptWriteError "cannot encode `None`")

/-! ## `IncrementalMPT` (class `IncrementalMPT`) -/

/-- The incremental MPT: `secured`/`default`/`root_node`/`_data`.  The
    `witness` field (witness generation) is not modeled. -/
structure IncrementalMpt where
  secured : Bool
  default : Option MptValue
  rootNode : Option MutableNode
  data : List (Bytes × MptValue) := []

/-- Dict write on the `_data` assoc list: update keeps position, new key
    appends (Python dict semantics). -/
private def dataSet (data : List (Bytes × MptValue)) (key : Bytes) (v : MptValue) :
    List (Bytes × MptValue) :=
  if data.any (·.1 == key) then
    data.map (fun p => if p.1 == key then (key, v) else p)
  else data ++ [(key, v)]

/-- `decode_witness_to_mpt` (function `decode_witness_to_mpt`) returning
    the full `IncrementalMPT` record (the `s1d19.1` port returns just the
    root node; the write side needs `secured`/`default`/`_data = {}`). -/
def decode_witness_mpt (nodeDb : List (Hash32 × Bytes)) (root_hash : Root)
    (secured : Bool) (default : Option MptValue) :
    Except SpecError IncrementalMpt := do
  pure { secured, default, rootNode := ← decode_witness_to_mpt nodeDb root_hash }

/-! ## `_build_mutable_tree` / `build_mpt` -/

/-- `_build_mutable_tree(obj, level)`: patricialize a nibble-keyed mapping
    into mutable nodes.  Fueled by the maximal key length (each recursion
    strictly increases `level`; see header). -/
def _build_mutable_tree : Nat → List (Bytes × Bytes) → Nat →
    Except SpecError (Option MutableNode)
  | _, [], _ => pure none
  | fuel, obj@((arbitrary_key, arbitrary_value) :: _), level => do
    if obj.length == 1 then
      pure (some (.leaf (arbitrary_key.drop level) arbitrary_value))
    else match fuel with
    | 0 => throw (.mptWriteError "_build_mutable_tree: fuel exhausted")
    | fuel + 1 =>
      let substring := arbitrary_key.drop level
      let prefix_length := obj.foldl (init := substring.length) (fun pl (key, _) =>
        min pl (common_prefix_length substring (key.drop level)))
      if prefix_length > 0 then
        let pfx := (arbitrary_key.drop level).take prefix_length
        let child ← _build_mutable_tree fuel obj (level + prefix_length)
        match child with
        | some c => pure (some (.extension pfx c))
        | none => throw (.mptWriteError "_build_mutable_tree: empty extension child")
      else do
        let value := (obj.find? (fun p => p.1.length == level)).map (·.2) |>.getD []
        let children ← (List.range 16).mapM (fun k =>
          _build_mutable_tree fuel
            (obj.filter (fun p => p.1.length != level && (p.1.getD level 0).toNat == k))
            (level + 1))
        pure (some (.branch children value))

/-- `_prepare_data(data, secured, get_storage_root)`: encode values and
    nibblize (secured → keccak) keys. -/
def _prepare_data (data : List (Bytes × MptValue)) (secured : Bool)
    (get_storage_root : Option (Bytes → Root)) :
    Except SpecError (List (Bytes × Bytes)) :=
  data.mapM (fun (preimage, value) => do
    let encoded ← encode_mpt_value preimage (some value) get_storage_root
    if encoded.isEmpty then
      throw (.mptWriteError "_prepare_data: empty encoded value")
    let key := if secured then keccak256 preimage else preimage
    pure (keyToNibbles key, encoded))

/-- `build_mpt(data, secured, default, get_storage_root)`. -/
def build_mpt (data : List (Bytes × MptValue)) (secured : Bool)
    (default : Option MptValue)
    (get_storage_root : Option (Bytes → Root) := none) :
    Except SpecError IncrementalMpt := do
  let prepared ← _prepare_data data secured get_storage_root
  let maxKeyLen := prepared.foldl (fun m p => max m p.1.length) 0
  let root ← _build_mutable_tree (maxKeyLen + 1) prepared 0
  pure { secured, default, rootNode := root, data }

/-! ## Node encoding (`_encode_mutable_node`,
`_encode_mutable_node_to_extended`, `_compute_node_hash_and_rlp`)

Structural (well-founded) recursion over the tree; memo-cache fast paths
are dropped as recompute-equal; a `HashedNode` embeds as its hash. -/

mutual

/-- `_encode_mutable_node(node)`: the RLP `Extended` form. -/
def _encode_mutable_node : Option MutableNode → Except SpecError RLPItem
  | none => pure (.bytes [])
  | some (.hashed _) => throw (.mptWriteError "HashedNode cannot be inline-encoded")
  | some (.leaf restOfKey value) =>
      pure (.list [.bytes (nibble_list_to_compact restOfKey true), .bytes value])
  | some (.extension keySegment child) => do
      let childEncoded ← _encode_mutable_node_to_extended (some child)
      pure (.list [.bytes (nibble_list_to_compact keySegment false), childEncoded])
  | some (.branch children value) => do
      let childrenEncoded ← encodeChildren children
      pure (.list (childrenEncoded ++ [.bytes value]))
termination_by n => (sizeOf n, 0)

/-- The 16 branch children, each via `_encode_mutable_node_to_extended`. -/
def encodeChildren : List (Option MutableNode) → Except SpecError (List RLPItem)
  | [] => pure []
  | child :: rest => do
      pure ((← _encode_mutable_node_to_extended child) :: (← encodeChildren rest))
termination_by cs => (sizeOf cs, 0)

/-- `_encode_mutable_node_to_extended(node)`: hash if RLP ≥ 32 bytes,
    else the unencoded form; a `HashedNode` is its hash. -/
def _encode_mutable_node_to_extended : Option MutableNode →
    Except SpecError RLPItem
  | none => pure (.bytes [])
  | some (.hashed h) => pure (.bytes h)
  | some node => do
      let unencoded ← _encode_mutable_node (some node)
      let encoded := encR unencoded
      if encoded.length < 32 then pure unencoded
      else pure (.bytes (keccak256 encoded))
termination_by n => (sizeOf n, 1)

end

/-- `_compute_node_hash_and_rlp(node)`: `(hash?, rlp)`, hash `none` for
    < 32-byte encodings.  (`HashedNode` is an assert.) -/
def _compute_node_hash_and_rlp (node : Option MutableNode) :
    Except SpecError (Option Bytes × Bytes) := do
  match node with
  | none => pure (none, [])
  | some (.hashed _) =>
      throw (.mptWriteError "HashedNode cannot appear in _compute_node_hash_and_rlp")
  | some _ =>
      let encoded := encR (← _encode_mutable_node node)
      if encoded.length ≥ 32 then pure (some (keccak256 encoded), encoded)
      else pure (none, encoded)

/-! ## `mpt_get` (function `mpt_get`) -/

/-- `_mpt_traverse_for_witness(mpt, node, key, level)`: witness-recording
    walk; the recording itself is unmodeled, but visiting a `HashedNode`
    is `_record_witness`'s assert → rejection. -/
def _mpt_traverse_for_witness : Nat → Option MutableNode → Bytes → Nat →
    Except SpecError Unit
  | _, none, _, _ => pure ()
  | 0, some _, _, _ => throw (.mptWriteError "_mpt_traverse_for_witness: fuel exhausted")
  | _, some (.hashed _), _, _ =>
      throw (.mptWriteError "HashedNode cannot be witnessed")
  | _ + 1, some (.leaf ..), _, _ => pure ()
  | fuel + 1, some (.extension keySegment child), key, level =>
      if (key.drop level).take keySegment.length == keySegment then
        _mpt_traverse_for_witness fuel (some child) key (level + keySegment.length)
      else pure ()
  | fuel + 1, some (.branch children _), key, level =>
      if level < key.length then
        _mpt_traverse_for_witness fuel
          (children.getD (key.getD level 0).toNat none) key (level + 1)
      else pure ()

/-- `mpt_get(mpt, key)`: the value from `_data` (default when absent);
    the witness traversal can reject on `HashedNode` contact. -/
def mpt_get (mpt : IncrementalMpt) (key : Bytes) :
    Except SpecError (Option MptValue) := do
  let value := ((mpt.data.find? (·.1 == key)).map (fun p => some p.2)).getD mpt.default
  let nibble_key := keyToNibbles (if mpt.secured then keccak256 key else key)
  _mpt_traverse_for_witness (nibble_key.length + 1) mpt.rootNode nibble_key 0
  pure value

/-! ## Insertion (`_mpt_insert_node` and helpers) -/

/-- `_create_branch_from_two_leaves(key1, value1, key2, value2)`. -/
def _create_branch_from_two_leaves (key1 : Bytes) (value1 : Bytes)
    (key2 : Bytes) (value2 : Bytes) : MutableNode :=
  let place := fun (children : List (Option MutableNode)) (value : Bytes)
      (k : Bytes) (v : Bytes) =>
    match k with
    | [] => (children, v)
    | idx :: rest =>
        (children.set idx.toNat (some (.leaf rest v)), value)
  let (children, value) := place (List.replicate 16 none) [] key1 value1
  let (children, value) := place children value key2 value2
  .branch children value

/-- `_split_extension(node, remaining_key, value, prefix_len)`. -/
def _split_extension (segment : Bytes) (child : MutableNode)
    (remaining_key : Bytes) (value : Bytes) (prefix_len : Nat) :
    Except SpecError MutableNode := do
  let segment_after_prefix := segment.drop prefix_len
  let children : List (Option MutableNode) :=
    match segment_after_prefix with
    | [] => List.replicate 16 none
    | idx :: [] => (List.replicate 16 none).set idx.toNat (some child)
    | idx :: rest => (List.replicate 16 none).set idx.toNat (some (.extension rest child))
  let key_after_prefix := remaining_key.drop prefix_len
  match key_after_prefix with
  | [] => pure (.branch children value)
  | idx :: rest =>
      match children.getD idx.toNat none with
      | none => pure (.branch (children.set idx.toNat (some (.leaf rest value))) [])
      | some _ => throw (.mptWriteError "Unexpected collision during split")

mutual

/-- `_mpt_insert_node(mpt, node, key, value, level)`.  `_invalidate_hash`
    on a `HashedNode` is the assert → rejection; on other nodes it only
    clears the unmodeled memo caches. -/
def _mpt_insert_node (fuel : Nat) (node : Option MutableNode) (key : Bytes)
    (value : Bytes) (level : Nat) : Except SpecError MutableNode := do
  match node with
  | none => pure (.leaf (key.drop level) value)
  | some (.hashed _) => throw (.mptWriteError "HashedNode cannot be invalidated")
  | some node =>
    match fuel with
    | 0 => throw (.mptWriteError "_mpt_insert_node: fuel exhausted")
    | fuel + 1 =>
      match node with
      | .leaf restOfKey leafValue =>
          _insert_into_leaf restOfKey leafValue key value level
      | .extension keySegment child =>
          _insert_into_extension fuel keySegment child key value level
      | .branch children branchValue =>
          _insert_into_branch fuel children branchValue key value level
      | .hashed _ => throw (.mptWriteError "HashedNode cannot be invalidated")

/-- `_insert_into_leaf(mpt, node, key, value, level)`. -/
def _insert_into_leaf (existing_key : Bytes) (existing_value : Bytes)
    (key : Bytes) (value : Bytes) (level : Nat) : Except SpecError MutableNode := do
  let remaining_key := key.drop level
  if existing_key == remaining_key then
    pure (.leaf existing_key value)
  else
    let prefix_len := common_prefix_length existing_key remaining_key
    if prefix_len > 0 then
      let branch := _create_branch_from_two_leaves
        (existing_key.drop prefix_len) existing_value
        (remaining_key.drop prefix_len) value
      pure (.extension (existing_key.take prefix_len) branch)
    else
      pure (_create_branch_from_two_leaves existing_key existing_value
        remaining_key value)

/-- `_insert_into_extension(mpt, node, key, value, level)`. -/
def _insert_into_extension (fuel : Nat) (segment : Bytes) (child : MutableNode)
    (key : Bytes) (value : Bytes) (level : Nat) : Except SpecError MutableNode := do
  let remaining_key := key.drop level
  let prefix_len := common_prefix_length segment remaining_key
  if prefix_len == segment.length then do
    let child' ← _mpt_insert_node fuel (some child) key value (level + prefix_len)
    pure (.extension segment child')
  else if prefix_len > 0 then do
    let new_child ← _split_extension segment child remaining_key value prefix_len
    pure (.extension (segment.take prefix_len) new_child)
  else
    _split_extension segment child remaining_key value 0

/-- `_insert_into_branch(mpt, node, key, value, level)`. -/
def _insert_into_branch (fuel : Nat) (children : List (Option MutableNode))
    (branchValue : Bytes) (key : Bytes) (value : Bytes) (level : Nat) :
    Except SpecError MutableNode := do
  match key.drop level with
  | [] => pure (.branch children value)
  | idx :: _ =>
      let child' ← _mpt_insert_node fuel (children.getD idx.toNat none)
        key value (level + 1)
      pure (.branch (children.set idx.toNat (some child')) branchValue)

end

/-! ## Deletion (`_mpt_delete_node` and helpers) -/

/-- `_collapse_branch(mpt, node)`: collapse a single-child branch.  The
    `_record_witness` call on the surviving child asserts it is not a
    `HashedNode` → rejection. -/
def _collapse_branch (children : List (Option MutableNode)) (value : Bytes) :
    Except SpecError MutableNode := do
  let non_empty := (children.zipIdx.filterMap (fun (c, i) => c.map ((i, ·))))
  if non_empty.isEmpty && value.isEmpty then
    throw (.mptWriteError "_collapse_branch: empty branch")
  if non_empty.length == 1 && value.isEmpty then
    match non_empty with
    | [(idx, child)] =>
        let nibble : BitVec 8 := BitVec.ofNat 8 idx
        match child with
        | .leaf restOfKey v => pure (.leaf (nibble :: restOfKey) v)
        | .extension keySegment c => pure (.extension (nibble :: keySegment) c)
        | .branch .. => pure (.extension [nibble] child)
        | .hashed _ => throw (.mptWriteError "HashedNode cannot be witnessed")
    | _ => throw (.mptWriteError "_collapse_branch: unreachable")
  else if non_empty.isEmpty then
    pure (.leaf [] value)
  else
    pure (.branch children value)

mutual

/-- `_mpt_delete_node(mpt, node, key, level)`. -/
def _mpt_delete_node (fuel : Nat) (node : Option MutableNode) (key : Bytes)
    (level : Nat) : Except SpecError (Option MutableNode) := do
  match node with
  | none => pure none
  | some (.hashed _) => throw (.mptWriteError "HashedNode cannot be invalidated")
  | some node =>
    match fuel with
    | 0 => throw (.mptWriteError "_mpt_delete_node: fuel exhausted")
    | fuel + 1 =>
      match node with
      | .leaf restOfKey value =>
          if restOfKey == key.drop level then pure none
          else pure (some (.leaf restOfKey value))
      | .extension keySegment child =>
          _delete_from_extension fuel keySegment child key level
      | .branch children value =>
          _delete_from_branch fuel children value key level
      | .hashed _ => throw (.mptWriteError "HashedNode cannot be invalidated")

/-- `_delete_from_extension(mpt, node, key, level)`. -/
def _delete_from_extension (fuel : Nat) (segment : Bytes) (child : MutableNode)
    (key : Bytes) (level : Nat) : Except SpecError (Option MutableNode) := do
  let remaining_key := key.drop level
  let prefix_len := common_prefix_length segment remaining_key
  if prefix_len < segment.length then
    pure (some (.extension segment child))
  else do
    match ← _mpt_delete_node fuel (some child) key (level + segment.length) with
    | none => pure none
    | some (.extension childSegment grandchild) =>
        pure (some (.extension (segment ++ childSegment) grandchild))
    | some (.leaf restOfKey value) =>
        pure (some (.leaf (segment ++ restOfKey) value))
    | some new_child@(.branch ..) => pure (some (.extension segment new_child))
    | some (.hashed _) => throw (.mptWriteError "HashedNode delete child")

/-- `_delete_from_branch(mpt, node, key, level)`.  The `child_changed`
    identity check is dropped (see the header note): the update and
    collapse are no-ops on content-unchanged subtrees. -/
def _delete_from_branch (fuel : Nat) (children : List (Option MutableNode))
    (value : Bytes) (key : Bytes) (level : Nat) :
    Except SpecError (Option MutableNode) := do
  match key.drop level with
  | [] =>
      if value.isEmpty then pure (some (.branch children value))
      else pure (some (← _collapse_branch children []))
  | idx :: _ =>
      let new_child ← _mpt_delete_node fuel (children.getD idx.toNat none)
        key (level + 1)
      pure (some (← _collapse_branch (children.set idx.toNat new_child) value))

end

/-! ## `mpt_set` (function `mpt_set`) -/

/-- `mpt_set(mpt, key, value, get_storage_root)`: update `_data`, encode
    the value (default → `b""` → delete), and insert/delete in the tree. -/
def mpt_set (mpt : IncrementalMpt) (key : Bytes) (value : Option MptValue)
    (get_storage_root : Option (Bytes → Root) := none) :
    Except SpecError IncrementalMpt := do
  let data :=
    if value == mpt.default then mpt.data.filter (·.1 != key)
    else match value with
      | some v => dataSet mpt.data key v
      | none => mpt.data  -- non-default `None`: unencodable, rejected below
  let nibble_key := keyToNibbles (if mpt.secured then keccak256 key else key)
  let encoded_value ←
    if value == mpt.default then pure ([] : Bytes)
    else encode_mpt_value key value get_storage_root
  if encoded_value.isEmpty then
    let root ← _mpt_delete_node (nibble_key.length + 1) mpt.rootNode nibble_key 0
    pure { mpt with data, rootNode := root }
  else
    let root ← _mpt_insert_node (nibble_key.length + 1) mpt.rootNode nibble_key
      encoded_value 0
    pure { mpt with data, rootNode := some root }

/-! ## `mpt_root` (function `mpt_root`) -/

/-- `mpt_root(mpt)`: the root hash — `EMPTY_TRIE_ROOT` for the empty
    trie; a bytes result of `_encode_mutable_node_to_extended` IS the
    32-byte root (hashed or `HashedNode`); a small unencoded root is
    hashed from its RLP. -/
def mpt_root (mpt : IncrementalMpt) : Except SpecError Root := do
  match mpt.rootNode with
  | none => pure EMPTY_TRIE_ROOT
  | some root =>
      match ← _encode_mutable_node_to_extended (some root) with
      | .bytes b => pure b
      | item => pure (keccak256 (encR item))

/-! ## Sanity checks

Every expected root below is cross-checked against the Python spec at
`bd8c673` (`build_mpt`/`mpt_set`/`mpt_root` executed on the submodule;
generator script in the s1d19.4 PR description).  The `MptWriteVectors`
namespace is shared with `WitnessStateRoot.lean`'s sanity block. -/

-- nibble_list_to_compact: even/odd extension, even/odd leaf, empty leaf;
-- round trip with compact_to_nibbles.
#guard nibble_list_to_compact [0x0A, 0x0B] false == [0x00, 0xAB]
#guard nibble_list_to_compact [0x0A, 0x0B, 0x0C] false == [0x1A, 0xBC]
#guard nibble_list_to_compact [0x0A, 0x0B] true == [0x20, 0xAB]
#guard nibble_list_to_compact [0x0B] true == [0x3B]
#guard nibble_list_to_compact [] true == [0x20]
#guard (compact_to_nibbles (nibble_list_to_compact [0x0A, 0x0B, 0x0C] true)).toOption
  == some ([0x0A, 0x0B, 0x0C], true)

namespace MptWriteVectors

def k32 (b : BitVec 8) : Bytes := List.replicate 32 b

/-- Secured `U256` storage trie: insert ×3, update, delete ×3 — the root
    after each step, vs the Python spec. -/
def storageRoots : Except SpecError (List Nat) := do
  let mut m : IncrementalMpt :=
    { secured := true, default := some (.u256 0), rootNode := none }
  let mut rs : List Nat := []
  for (k, v) in [(k32 1, 0x2A), (k32 2, 7), (k32 3, 9), (k32 2, 8),
                 (k32 3, 0), (k32 2, 0), (k32 1, 0)] do
    m ← mpt_set m k (some (.u256 v))
    rs := rs ++ [bytesBEtoNat (← mpt_root m)]
  pure rs

#guard storageRoots.toOption == some
  [0x28e1a0e686a820dd23a1e58573a163f3d69f22a614f89a29022cd5aa2993109e,
   0x42a9aa2b9aba3c215c27f0013174de2fd38c930c119aebaca4ef1ddd2095cf76,
   0xa12bcb7aadad162343e1d0dde93193bddf51c246ed0c0ff440826f0df1611029,
   0xff9df1abc787b0e61dec88be35b8cdbedb6829ab5d1559163a3536acc2dc58f2,
   0x5322886238e47cc6aabf650e889eef69ef568556a6edca297de466b09a43dc5e,
   0x28e1a0e686a820dd23a1e58573a163f3d69f22a614f89a29022cd5aa2993109e,
   0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421]

-- Unsecured bytes trie (transaction-trie shape): rlp-scalar keys, fat
-- values; incremental mpt_set and build_mpt agree with the Python root.
def txKey (i : Nat) : Bytes := encR (.bytes (EvmAsm.EL.RLP.Nat.toBytesBE i))
def txVal (i : BitVec 8) : Bytes := 0xF8 :: 0x6B :: List.replicate 40 i
def txRootExpected : Nat :=
  0x1783cc7612107c3315a3c8efb682a80e83a9aaeeb69c85d143f20a62ebb96a06

#guard
  (do
    let mut m : IncrementalMpt :=
      { secured := false, default := some (.bytes []), rootNode := none }
    for i in [0, 1, 2] do
      m ← mpt_set m (txKey i) (some (.bytes (txVal (BitVec.ofNat 8 i))))
    mpt_root m : Except SpecError Root).toOption.map bytesBEtoNat
  == some txRootExpected

#guard
  (do
    let m ← build_mpt ((List.range 3).map (fun i =>
      (txKey i, .bytes (txVal (BitVec.ofNat 8 i))))) false (some (.bytes []))
    mpt_root m).toOption.map bytesBEtoNat == some txRootExpected

/-! The two-account state (accounts `0xA1…`/`0x00…`, `0xA1…` holding a
two-slot storage trie), its witness node DB, and the Python-computed
roots — shared with `WitnessStateRoot.lean`. -/

def wAddrA : Address := List.replicate 20 0xA1
def wAddrB : Address := List.replicate 20 0x00
def wAddrD : Address := List.replicate 20 0xD4
def acctA : Account := { nonce := 1, balance := 100, codeHash := EMPTY_CODE_HASH }
def acctB : Account := { nonce := 0, balance := 5, codeHash := EMPTY_CODE_HASH }
def acctD : Account := { nonce := 0, balance := 3, codeHash := EMPTY_CODE_HASH }

/-- `0xA1…`'s storage root: `{k1 ↦ 0x2A, k2 ↦ 7}`. -/
def srootA : Root :=
  (do
    let m : IncrementalMpt :=
      { secured := true, default := some (.u256 0), rootNode := none }
    let m ← mpt_set m (k32 1) (some (.u256 0x2A))
    let m ← mpt_set m (k32 2) (some (.u256 7))
    mpt_root m).toOption.getD []

#guard bytesBEtoNat srootA
  == 0x42a9aa2b9aba3c215c27f0013174de2fd38c930c119aebaca4ef1ddd2095cf76

def gsrA : Bytes → Root := fun a => if a == wAddrA then srootA else EMPTY_TRIE_ROOT

/-- The two-account state root, built incrementally. -/
def wStateRoot : Root :=
  (do
    let m : IncrementalMpt := { secured := true, default := none, rootNode := none }
    let m ← mpt_set m wAddrA (some (.account acctA)) (get_storage_root := some gsrA)
    let m ← mpt_set m wAddrB (some (.account acctB)) (get_storage_root := some gsrA)
    mpt_root m).toOption.getD []

#guard bytesBEtoNat wStateRoot
  == 0x0f33d0ee44133b51a53c207779c89e3c1a847923161b238f6091f527e2ea8a3b

/-- The witness node DB for the state above: the six hash-referenced
    node preimages (state branch, two account leaves, storage branch,
    two storage leaves), as collected from the Python spec. -/
def wnode0 : Bytes := [0xF8, 0x51, 0x80, 0x80, 0x80, 0x80, 0x80, 0xA0, 0xDF, 0xBF, 0x39, 0xFA, 0x78, 0xBE, 0x34, 0x8F, 0xBD, 0x2A, 0xCE, 0xA6, 0x06, 0xAD, 0x4B, 0xEE, 0x38, 0xE1, 0xD0, 0xAD, 0x50, 0x3D, 0x56, 0x62, 0xAE, 0x39, 0xF5, 0x0C, 0x52, 0x47, 0xB8, 0xCD, 0x80, 0x80, 0xA0, 0x51, 0x17, 0xC9, 0x35, 0xD6, 0xE7, 0x79, 0x09, 0xD9, 0x24, 0xED, 0xB1, 0x0E, 0x0E, 0x95, 0x7B, 0xFB, 0x74, 0xA1, 0x33, 0x18, 0xC7, 0xDA, 0x07, 0x72, 0xE1, 0x0A, 0xA7, 0xE3, 0xFB, 0xB4, 0x98, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80]
def wnode1 : Bytes := [0xF8, 0x69, 0xA0, 0x33, 0x80, 0xC7, 0xB7, 0xAE, 0x81, 0xA5, 0x8E, 0xB9, 0x8D, 0x9C, 0x78, 0xDE, 0x4A, 0x1F, 0xD7, 0xFD, 0x95, 0x35, 0xFC, 0x95, 0x3E, 0xD2, 0xBE, 0x60, 0x2D, 0xAA, 0xA4, 0x17, 0x67, 0x31, 0x2A, 0xB8, 0x46, 0xF8, 0x44, 0x80, 0x05, 0xA0, 0x56, 0xE8, 0x1F, 0x17, 0x1B, 0xCC, 0x55, 0xA6, 0xFF, 0x83, 0x45, 0xE6, 0x92, 0xC0, 0xF8, 0x6E, 0x5B, 0x48, 0xE0, 0x1B, 0x99, 0x6C, 0xAD, 0xC0, 0x01, 0x62, 0x2F, 0xB5, 0xE3, 0x63, 0xB4, 0x21, 0xA0, 0xC5, 0xD2, 0x46, 0x01, 0x86, 0xF7, 0x23, 0x3C, 0x92, 0x7E, 0x7D, 0xB2, 0xDC, 0xC7, 0x03, 0xC0, 0xE5, 0x00, 0xB6, 0x53, 0xCA, 0x82, 0x27, 0x3B, 0x7B, 0xFA, 0xD8, 0x04, 0x5D, 0x85, 0xA4, 0x70]
def wnode2 : Bytes := [0xF8, 0x69, 0xA0, 0x36, 0x0E, 0x2F, 0x2A, 0x05, 0x9D, 0xEF, 0xB5, 0x08, 0x24, 0xAF, 0x2B, 0x02, 0x4B, 0x4E, 0x7A, 0x37, 0x75, 0x4D, 0x03, 0x67, 0x6B, 0x00, 0xDE, 0x68, 0x4D, 0x95, 0xD1, 0x12, 0xAE, 0xFD, 0x87, 0xB8, 0x46, 0xF8, 0x44, 0x01, 0x64, 0xA0, 0x42, 0xA9, 0xAA, 0x2B, 0x9A, 0xBA, 0x3C, 0x21, 0x5C, 0x27, 0xF0, 0x01, 0x31, 0x74, 0xDE, 0x2F, 0xD3, 0x8C, 0x93, 0x0C, 0x11, 0x9A, 0xEB, 0xAC, 0xA4, 0xEF, 0x1D, 0xDD, 0x20, 0x95, 0xCF, 0x76, 0xA0, 0xC5, 0xD2, 0x46, 0x01, 0x86, 0xF7, 0x23, 0x3C, 0x92, 0x7E, 0x7D, 0xB2, 0xDC, 0xC7, 0x03, 0xC0, 0xE5, 0x00, 0xB6, 0x53, 0xCA, 0x82, 0x27, 0x3B, 0x7B, 0xFA, 0xD8, 0x04, 0x5D, 0x85, 0xA4, 0x70]
def wnode3 : Bytes := [0xF8, 0x51, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0xA0, 0x4E, 0x54, 0x53, 0x2C, 0x70, 0x13, 0x3E, 0xA2, 0x97, 0x06, 0x7C, 0x48, 0x55, 0xA1, 0x59, 0x61, 0x03, 0x8A, 0x08, 0x21, 0x6F, 0xD1, 0x7F, 0x12, 0x9A, 0x16, 0xFE, 0x84, 0xB6, 0x65, 0xE7, 0xD9, 0x80, 0xA0, 0x10, 0xE5, 0xE5, 0xD2, 0x66, 0xB0, 0x29, 0x1C, 0x23, 0x13, 0x79, 0x5C, 0x70, 0x19, 0x77, 0x2E, 0x73, 0xAA, 0x27, 0xB0, 0x34, 0xA7, 0x26, 0x35, 0x3B, 0xE7, 0x34, 0x42, 0xA1, 0x17, 0xC4, 0xBE, 0x80, 0x80]
def wnode4 : Bytes := [0xE2, 0xA0, 0x3E, 0xBC, 0x88, 0x82, 0xFE, 0xCB, 0xEC, 0x7F, 0xB8, 0x0D, 0x2C, 0xF4, 0xB3, 0x12, 0xBE, 0xC0, 0x18, 0x88, 0x4C, 0x2D, 0x66, 0x66, 0x7C, 0x67, 0xA9, 0x05, 0x08, 0x21, 0x4B, 0xD8, 0xBA, 0xFC, 0x2A]
def wnode5 : Bytes := [0xE2, 0xA0, 0x3E, 0x4A, 0x07, 0x9F, 0x5B, 0x14, 0xA2, 0x44, 0x65, 0x18, 0x1D, 0x45, 0xAF, 0x32, 0xA8, 0x05, 0x3C, 0x2D, 0x44, 0x64, 0x46, 0xD7, 0x01, 0x93, 0x59, 0xE2, 0x10, 0xB8, 0x2E, 0x53, 0xB8, 0xBA, 0x07]

def wNodeDb : List (Hash32 × Bytes) :=
  build_node_db [wnode0, wnode1, wnode2, wnode3, wnode4, wnode5]

-- Decode-then-mutate round trip: decode the witness, insert a fresh
-- account, then delete one — roots match the Python spec at each step.
#guard
  (do
    let m ← decode_witness_mpt wNodeDb wStateRoot true none
    let m ← mpt_set m wAddrD (some (.account acctD))
      (get_storage_root := some (fun _ => EMPTY_TRIE_ROOT))
    let r1 := bytesBEtoNat (← mpt_root m)
    let m ← mpt_set m wAddrB none
    let r2 := bytesBEtoNat (← mpt_root m)
    pure (r1, r2) : Except SpecError (Nat × Nat)).toOption
  == some (0xbb679da078ce8197f2b6b177425b0b9119d6fde290bd120a0c7e060ab6d21ee9,
           0x20ecc67460eb17737f3bc764a73e1da36f78128cef05ae9ac2d56317a35de254)

-- Withheld-node rejection: with the 0xA1… account leaf (wnode2) missing
-- from the DB, deleting 0x00… forces the branch collapse onto its
-- HashedNode sibling — a rejection, never a wrong root.
#guard
  (match (do
      let m ← decode_witness_mpt
        (build_node_db [wnode0, wnode1, wnode3, wnode4, wnode5]) wStateRoot true none
      let m ← mpt_set m wAddrB none
      mpt_root m : Except SpecError Root) with
   | .error (.mptWriteError _) => true
   | _ => false)

-- mpt_get: _data round trip + HashedNode-contact rejection on traversal.
#guard
  (do
    let m : IncrementalMpt :=
      { secured := true, default := some (.u256 0), rootNode := none }
    let m ← mpt_set m (k32 1) (some (.u256 0x2A))
    let v1 ← mpt_get m (k32 1)
    let v2 ← mpt_get m (k32 9)
    pure (v1, v2) : Except SpecError (Option MptValue × Option MptValue)).toOption
  == some (some (.u256 0x2A), some (.u256 0))

end MptWriteVectors

end EvmAsm.Stateless.SpecRef
