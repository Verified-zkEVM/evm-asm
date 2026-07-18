/-
  EvmAsm.Stateless.SpecRef.IncrementalMpt

  Port of the witness-decoding (read) side of
  `execution-specs/src/ethereum/forks/amsterdam/incremental_mpt.py`
  (`@tests-zkevm@v0.5.0`, `bd8c673`):

  * `compact_to_nibbles`    (function `compact_to_nibbles`)
  * `_resolve_child_ref`    (function `_resolve_child_ref`)
  * `_decode_witness_node`  (function `_decode_witness_node`)
  * `decode_witness_to_mpt` (function `decode_witness_to_mpt`)

  This is the MPT witness-verification core (obligation #7, bead
  `evm-asm-s1d19.1`; scope: docs/agents/specref-execution-seam-scope.md).
  The `MutableNode` type these functions produce lives in
  `WitnessState.lean` (a layout inversion vs. the Python modules, kept to
  avoid churning that file); `trieLookup` there walks the trees decoded
  here.  The *write* side of `incremental_mpt.py` (`mpt_set`, `mpt_root`,
  node encoding) is bead `s1d19.4`.

  ## Authentication semantics

  `build_node_db` keys every witness preimage by its keccak-256 hash, so a
  node fetched from the DB *by hash* is authenticated by construction: the
  fetched bytes hash to the requested key (keccak collision resistance is
  the standing modeling assumption — this models the authenticated read,
  it does not prove binding).  `decode_witness_to_mpt` anchors the walk at
  `node_db[root_hash]` — a missing root is a `KeyError` in Python, a
  rejection here — and `_resolve_child_ref` resolves every 32-byte child
  reference by DB hash lookup.  Children *absent* from the DB become
  `HashedNode` placeholders; that is not a decode failure (the real spec
  fails only if execution actually reaches one — `trieLookup` then errors
  with `unresolvedHashedNode`).  So an authenticated read returns the true
  value, and a missing or wrong-hash node produces a rejection, never a
  wrong value.

  ## Modeling notes

  * The Python recursion is unbounded; Lean requires a decreasing measure,
    so the mutual decoder carries fuel.  `decodeFuel` over-approximates
    the deepest possible acyclic walk (see its docstring), so exhaustion
    is reachable only on a node graph with a reference cycle — which
    requires a keccak fixpoint cycle among the witness preimages, is
    computationally infeasible, and would make the Python spec diverge.
    We reject (`witnessNodeMalformed`) instead of diverging: still "never
    a wrong value".
  * Python resolves an *inline* child by re-encoding the decoded RLP item
    and decoding it again (`_decode_witness_node(node_db,
    rlp.encode(child_ref))`); since `rlp.decode (rlp.encode x) = x`, we
    decode the already-decoded `RLPItem` directly (`decodeNodeItemAux`).
    The only observable difference is the Python-side `_hash`/`_rlp`
    caches, which this port does not model (they are pure memoization).
  * The Python `dict` node DB is modeled as the association list
    `build_node_db` produces; duplicate keys carry identical values
    (keys are `keccak256(entry)`), so first-match lookup coincides with
    the Python last-write-wins dict.
  * Python's `decode_witness_to_mpt` wraps the decoded root in an
    `IncrementalMPT` record together with `secured`/`default`/`_data`
    bookkeeping fields that only the write side consumes; until
    `s1d19.4` ports that side, we return the decoded `root_node`
    directly (`Option MutableNode`, `none` = empty trie), which is the
    exact input `trieLookup` takes.
-/

import EvmAsm.Stateless.SpecRef.WitnessState

namespace EvmAsm.Stateless.SpecRef

open EvmAsm.EL.RLP (RLPItem decodeFully)

/-! ## `compact_to_nibbles` (`incremental_mpt.py`, function `compact_to_nibbles`) -/

/-- Decode hex-prefix (compact) encoding into nibbles and the leaf flag.
    Inverse of `nibble_list_to_compact`.  Python indexes `compact[0]`
    unconditionally, so an empty input is an `IndexError` → rejection. -/
def compact_to_nibbles (compact : Bytes) : Except SpecError (Bytes × Bool) := do
  match compact with
  | [] => throw (.witnessNodeMalformed "compact_to_nibbles: empty input")
  | c0 :: rest =>
      let first_nibble := c0.toNat >>> 4
      let is_leaf := first_nibble &&& 0x02 ≠ 0
      let odd := first_nibble &&& 0x01 ≠ 0
      let tail := keyToNibbles rest
      let nibbles := if odd then BitVec.ofNat 8 (c0.toNat &&& 0x0F) :: tail else tail
      pure (nibbles, is_leaf)

/-! ## The node DB -/

/-- Python `node_db[h]` / `h in node_db` on the `build_node_db` dict.  The
    assoc list is keccak-keyed (`key = keccak256(value)`), so duplicate keys
    carry identical values and first-match lookup coincides with the dict. -/
def nodeDbLookup (nodeDb : List (Hash32 × Bytes)) (h : Bytes) : Option Bytes :=
  (nodeDb.find? (fun p => p.1 == h)).map (·.2)

/-- Fuel upper-bounding the recursion depth of an acyclic witness decode:
    a walk visits each DB entry at most once per path (revisiting = a
    reference cycle), and inline nesting inside one RLP node is bounded by
    that node's byte length, so `Σ (1 + entry.length)` over the DB plus the
    root node's own length is a strict over-approximation. -/
def decodeFuel (nodeDb : List (Hash32 × Bytes)) : Nat :=
  nodeDb.foldl (fun a p => a + p.2.length + 1) 1

mutual

/-- `_decode_witness_node` (`incremental_mpt.py`, function
    `_decode_witness_node`), stated over the decoded `RLPItem` (see the
    header's inline-child modeling note).  Every Python `assert` failure is
    a `witnessNodeMalformed` rejection. -/
def decodeNodeItemAux (fuel : Nat) (nodeDb : List (Hash32 × Bytes)) :
    RLPItem → Except SpecError (Option MutableNode)
  | .bytes b =>
      if b.isEmpty then pure none
      else throw (.witnessNodeMalformed "Expected empty node")
  | .list [pathItem, second] => do
      match fuel with
      | 0 => throw (.witnessNodeMalformed "fuel exhausted (node-graph cycle)")
      | fuel + 1 =>
        let path ← match pathItem with
          | .bytes p => pure p
          | .list _ => throw (.witnessNodeMalformed "node path must be bytes")
        let (nibbles, is_leaf) ← compact_to_nibbles path
        if is_leaf then
          match second with
          | .bytes value => pure (some (.leaf nibbles value))
          | .list _ => throw (.witnessNodeMalformed "leaf value must be bytes")
        else
          if nibbles.isEmpty then
            throw (.witnessNodeMalformed "ExtensionNode must have a non-empty path")
          match ← resolveChildRefAux fuel nodeDb second with
          | some child@(.branch ..) => pure (some (.extension nibbles child))
          | some child@(.hashed _) => pure (some (.extension nibbles child))
          | _ => throw (.witnessNodeMalformed "ExtensionNode child must be a BranchNode")
  | .list items => do
      match fuel with
      | 0 => throw (.witnessNodeMalformed "fuel exhausted (node-graph cycle)")
      | fuel + 1 =>
        if items.length ≠ 17 then
          throw (.witnessNodeMalformed "Invalid RLP node length")
        let children ← (items.take 16).mapM (resolveChildRefAux fuel nodeDb)
        -- `decoded[16]`: bytes → the branch value; a (nested-list) non-bytes
        -- 17th item degrades to `b""` in Python, mirrored here.
        let value := match items.getD 16 (.bytes []) with
          | .bytes v => v
          | .list _ => []
        let occupied := (children.countP (·.isSome)) + (if value.isEmpty then 0 else 1)
        if occupied < 2 then
          throw (.witnessNodeMalformed "BranchNode must have at least 2 occupied entries")
        pure (some (.branch children value))

/-- `_resolve_child_ref` (`incremental_mpt.py`, function
    `_resolve_child_ref`).  Bytes cases: empty → no child; 32 bytes → DB
    hash lookup (present → authenticated decode of the preimage, absent →
    `HashedNode` placeholder); any other length is an `assert` failure.
    List case: inline node, decoded directly. -/
def resolveChildRefAux (fuel : Nat) (nodeDb : List (Hash32 × Bytes)) :
    RLPItem → Except SpecError (Option MutableNode)
  | .bytes ref => do
      match fuel with
      | 0 => throw (.witnessNodeMalformed "fuel exhausted (node-graph cycle)")
      | fuel + 1 =>
        if ref.isEmpty then pure none
        else if ref.length ≠ 32 then
          throw (.witnessNodeMalformed "Unexpected child ref length")
        else
          match nodeDbLookup nodeDb ref with
          | some rlpBytes =>
              match decodeFully rlpBytes with
              | some item => decodeNodeItemAux fuel nodeDb item
              | none => throw (.witnessNodeMalformed "witness node RLP decode failed")
          | none => pure (some (.hashed ref))
  | .list items => do
      match fuel with
      | 0 => throw (.witnessNodeMalformed "fuel exhausted (node-graph cycle)")
      | fuel + 1 => decodeNodeItemAux fuel nodeDb (.list items)

end

/-- `_decode_witness_node(node_db, rlp_bytes)` from raw RLP bytes: RLP
    decode (a Python `DecodingError` → rejection), then the structural
    decode.  The Python-side `node_hash` computed for `len(rlp_bytes) ≥ 32`
    only feeds the unmodeled `_hash` memo cache. -/
def _decode_witness_node (nodeDb : List (Hash32 × Bytes)) (rlp_bytes : Bytes) :
    Except SpecError (Option MutableNode) := do
  match decodeFully rlp_bytes with
  | some item => decodeNodeItemAux (decodeFuel nodeDb + rlp_bytes.length) nodeDb item
  | none => throw (.witnessNodeMalformed "witness node RLP decode failed")

/-! ## `decode_witness_to_mpt` (`incremental_mpt.py`, function `decode_witness_to_mpt`) -/

/-- Decode the trie rooted at `root_hash` from the witness node DB — the
    root-anchored authenticated reconstruction (obligation #7).
    `EMPTY_TRIE_ROOT` denotes the empty trie (no root node); otherwise the
    root preimage MUST be in the DB (`node_db[root_hash]`, a `KeyError` →
    rejection in Python).  Returns the decoded `root_node`; unknown
    children inside it are `HashedNode` placeholders (see the header). -/
def decode_witness_to_mpt (nodeDb : List (Hash32 × Bytes)) (root_hash : Root) :
    Except SpecError (Option MutableNode) := do
  if root_hash == EMPTY_TRIE_ROOT then
    pure none
  else
    match nodeDbLookup nodeDb root_hash with
    | none => throw .witnessRootMissing
    | some root_rlp => _decode_witness_node nodeDb root_rlp

/-! ## Sanity checks

Hand-assembled RLP tries, checked end-to-end: `build_node_db` →
`decode_witness_to_mpt` → `trieLookup`. -/

private def enc (i : RLPItem) : Bytes := EvmAsm.EL.RLP.encode i

-- compact_to_nibbles: even extension (0x00 prefix), odd extension (0x1_),
-- even leaf (0x20), odd leaf (0x3_); empty input rejected.
#guard (compact_to_nibbles [0x00, 0xAB]).toOption == some ([0x0A, 0x0B], false)
#guard (compact_to_nibbles [0x1A, 0xBC]).toOption == some ([0x0A, 0x0B, 0x0C], false)
#guard (compact_to_nibbles [0x20, 0xAB]).toOption == some ([0x0A, 0x0B], true)
#guard (compact_to_nibbles [0x3B]).toOption == some ([0x0B], true)
#guard match compact_to_nibbles [] with
  | .error (.witnessNodeMalformed _) => true | _ => false

-- The empty trie decodes to no root node.
#guard match decode_witness_to_mpt [] EMPTY_TRIE_ROOT with
  | .ok none => true | _ => false

-- A non-empty root absent from the node DB is a rejection (KeyError):
-- root authentication is anchored, not best-effort.
#guard match decode_witness_to_mpt [] (List.replicate 32 0x11) with
  | .error .witnessRootMissing => true | _ => false

-- Single-leaf trie: leaf for key 0xAB (nibbles [A,B], compact 0x20AB),
-- value 0x99. Authenticated end-to-end read through the keccak-keyed DB.
private def leafAB : Bytes := enc (.list [.bytes [0x20, 0xAB], .bytes [0x99]])

#guard
  let db := build_node_db [leafAB]
  match decode_witness_to_mpt db (keccak256 leafAB) with
  | .ok root =>
      (match root with
       | some (.leaf [0x0A, 0x0B] [0x99]) => true
       | _ => false)
      && (trieLookup root [0xAB]).toOption == some (some [0x99])
      && (trieLookup root [0xAC]).toOption == some none
  | _ => false

-- Branch trie with two inline leaf children: keys 0xAB / 0xBB share no
-- prefix, so the root is a branch with leaves (compact 0x3B, odd leaf) at
-- indices 0xA and 0xB.
private def inlineLeafB : RLPItem := .list [.bytes [0x3B], .bytes [0x77]]
private def branchRoot : Bytes :=
  enc (.list ((List.range 16).map (fun i =>
    if i == 0x0A ∨ i == 0x0B then inlineLeafB else .bytes []) ++ [.bytes []]))

#guard
  let db := build_node_db [branchRoot]
  match decode_witness_to_mpt db (keccak256 branchRoot) with
  | .ok root =>
      (trieLookup root [0xAB]).toOption == some (some [0x77])
      && (trieLookup root [0xBB]).toOption == some (some [0x77])
      && (trieLookup root [0xCB]).toOption == some none
  | _ => false

-- Hash-referenced children: the same two-leaf shape, but with fat leaves
-- (RLP ≥ 32 bytes) referenced by hash. The 0xA child's preimage is in the
-- DB (authenticated decode); the 0xB child's is withheld, so it decodes to
-- a HashedNode placeholder — decoding succeeds, and only a read that
-- REACHES the withheld subtree errors (unresolvedHashedNode).
private def fatLeaf : Bytes :=
  enc (.list [.bytes [0x3B], .bytes (List.replicate 40 0x55)])
private def branchHashRefs : Bytes :=
  enc (.list ((List.range 16).map (fun i =>
    if i == 0x0A ∨ i == 0x0B then .bytes (keccak256 fatLeaf) else .bytes [])
    ++ [.bytes []]))

#guard
  let db := build_node_db [branchHashRefs, fatLeaf]
  let dbWithheld := build_node_db [branchHashRefs]  -- fatLeaf withheld
  (match decode_witness_to_mpt db (keccak256 branchHashRefs) with
   | .ok root => (trieLookup root [0xAB]).toOption
       == some (some (List.replicate 40 0x55))
   | _ => false)
  &&
  (match decode_witness_to_mpt dbWithheld (keccak256 branchHashRefs) with
   | .ok root =>
       -- both subtrees are placeholders; reaching either one errors
       (match trieLookup root [0xAB] with
        | .error .unresolvedHashedNode => true | _ => false)
       -- but a key routed to an EMPTY branch slot still reads `none`
       && (trieLookup root [0xCB]).toOption == some none
   | _ => false)

-- Extension node: keys 0xAB / 0xAA share nibble prefix [A]; root is an
-- extension (compact 0x1A, odd non-leaf) over an inline branch whose 0xB /
-- 0xA slots hold inline value-leaves (compact 0x20, empty rest-of-key).
private def inlineValueLeaf (v : BitVec 8) : RLPItem := .list [.bytes [0x20], .bytes [v]]
private def extRoot : Bytes :=
  enc (.list [.bytes [0x1A],
    .list ((List.range 16).map (fun i =>
      if i == 0x0A then inlineValueLeaf 0x66
      else if i == 0x0B then inlineValueLeaf 0x77
      else .bytes []) ++ [.bytes []])])

#guard
  let db := build_node_db [extRoot]
  match decode_witness_to_mpt db (keccak256 extRoot) with
  | .ok root =>
      (trieLookup root [0xAA]).toOption == some (some [0x66])
      && (trieLookup root [0xAB]).toOption == some (some [0x77])
      && (trieLookup root [0xBB]).toOption == some none
  | _ => false

-- Malformed nodes are rejections: an extension whose child is a leaf, a
-- branch with fewer than 2 occupied entries, an extension with an empty
-- path, and a child ref of invalid length.
#guard
  let extLeafChild := enc (.list [.bytes [0x1A], inlineValueLeaf 0x66])
  match decode_witness_to_mpt (build_node_db [extLeafChild]) (keccak256 extLeafChild) with
  | .error (.witnessNodeMalformed _) => true | _ => false

#guard
  let oneChildBranch := enc (.list ((List.range 16).map (fun i =>
    if i == 0x0A then inlineValueLeaf 0x66 else .bytes []) ++ [.bytes []]))
  match decode_witness_to_mpt (build_node_db [oneChildBranch]) (keccak256 oneChildBranch) with
  | .error (.witnessNodeMalformed _) => true | _ => false

#guard
  let emptyPathExt := enc (.list [.bytes [0x00], .bytes (List.replicate 32 0x22)])
  match decode_witness_to_mpt (build_node_db [emptyPathExt]) (keccak256 emptyPathExt) with
  | .error (.witnessNodeMalformed _) => true | _ => false

#guard
  let badRef := enc (.list ((List.range 16).map (fun i =>
    if i == 0x0A ∨ i == 0x0B then .bytes [0x01, 0x02] else .bytes []) ++ [.bytes []]))
  match decode_witness_to_mpt (build_node_db [badRef]) (keccak256 badRef) with
  | .error (.witnessNodeMalformed _) => true | _ => false

end EvmAsm.Stateless.SpecRef
