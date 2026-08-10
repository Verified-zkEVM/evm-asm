/-
  EvmAsm.Evm64.MptCorrespondence

  The spec-level bridge from the guest's RLP MPT-node representation
  (`MptNode` / `mptNodeIs`, `EvmAsm/Evm64/MptAssertions.lean`) to the
  SpecRef `MutableNode` tree that `trieLookup` walks
  (`EvmAsm/Stateless/SpecRef/WitnessState.lean`) — the one load-bearing
  missing abstraction identified in
  `docs/4ch8f-slstate-specref-correspondence.md` §4 (bead
  `evm-asm-4ch8f.75.3`).

  * `rlpToMutableNode` — decode one RLP-encoded trie node into a
    *shallow* `MutableNode` (child references stay symbolic `.hashed`
    nodes; the resolve closure through the node DB is
    `SpecRef.decode_witness_to_mpt`'s job, `IncrementalMpt.lean`). The
    skeleton is exactly `mptNodeKindSpec` (the proven spec mirror of the
    guest's `mpt_node_kind` discriminator), returning the node instead
    of the tag.
  * `alpha_node` — the abstraction function `MptNode → MutableNode`
    from the doc §4 sketch: leaf/extension paths carry their decoded
    nibble lists verbatim (both sides use nibbles-as-bytes), hash
    references become `.hashed` placeholders, empty branch slots become
    `none`.
  * `rlpToMutableNode_rlp` — the round-trip: for every well-formed
    `n : MptNode`, decoding `n.rlp` yields exactly `alpha_node n`. Since
    `mptNodeIs ptr n` asserts the bytes `n.rlp` (with `n.WF`), this is
    the statement "the guest's node assertion decodes to the SpecRef
    `MutableNode`" that `.29`'s walk specs need to relate guest nodes to
    `trieLookup`.

  Scope note (v1, same as `MptNode`): branch children and the extension
  child are hash-or-empty references only; the `< 32`-byte *inlined*
  child form (`mpt_branch_child` status 2) is bead `evm-asm-4ch8f.75.4`.
-/

import EvmAsm.Evm64.MptAssertions

namespace EvmAsm.Evm64

open EvmAsm.EL.RLP
open EvmAsm.Stateless.SpecRef (MutableNode)

/-! ## The decoder -/

/-- Decode one branch child slot (an RLP item of the 17-item list):
    empty bytes ⇒ no child, a 32-byte string ⇒ a symbolic `.hashed`
    reference. Anything else (an inlined `< 32`-byte child, a nested
    list) is out of the v1 vocabulary (bead `4ch8f.75.4`) ⇒ decode
    failure. -/
def rlpChildSlot : RLPItem → Option (Option MutableNode)
  | .bytes c =>
      if c = [] then some none
      else if c.length = 32 then some (some (.hashed c))
      else none
  | .list _ => none

/-- Decode an RLP-encoded trie node into a shallow SpecRef
    `MutableNode`. The skeleton is `mptNodeKindSpec`
    (`MptAssertions.lean`) — the guest's `mpt_node_kind` discriminator:
    item 2 exists ⇒ branch (then the 17 items are the 16 child slots and
    the value); otherwise a 2-item `[compact path, payload]` list is a
    leaf or extension by the hex-prefix flag of the path. -/
def rlpToMutableNode (bs : List (BitVec 8)) : Option MutableNode :=
  match decodeFully bs with
  | some (.list items) =>
    if 2 < items.length then
      if items.length = 17 then
        match (items.take 16).mapM rlpChildSlot, items.getD 16 (.bytes []) with
        | some children, .bytes v => some (.branch children v)
        | _, _ => none
      else none
    else
      match items with
      | [.bytes path, .bytes payload] =>
        match hpDecode path with
        | some (true, nibs) => some (.leaf nibs payload)
        | some (false, nibs) => some (.extension nibs (.hashed payload))
        | none => none
      | _ => none
  | _ => none

/-! ## The abstraction function -/

/-- `α_node` (doc §4): abstract one guest `MptNode` to a shallow SpecRef
    `MutableNode` — paths verbatim (nibbles-as-bytes on both sides),
    hash references to `.hashed` placeholders, empty branch slots to
    `none`. -/
def alpha_node : MptNode → MutableNode
  | .leaf p v => .leaf p v
  | .extension p c => .extension p (.hashed c)
  | .branch cs v =>
      .branch (cs.map fun c => if c = [] then none else some (.hashed c)) v

/-! ## The round-trip theorem -/

/-- Well-formed branch child lists decode slot-by-slot to `α_node`'s
    children. -/
theorem mapM_rlpChildSlot (cs : List (List (BitVec 8)))
    (h : ∀ c ∈ cs, c.length = 0 ∨ c.length = 32) :
    (cs.map RLPItem.bytes).mapM rlpChildSlot =
      some (cs.map fun c => if c = [] then none else some (.hashed c)) := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    have hrest := ih (fun c' hc' => h c' (by simp [hc']))
    rw [List.map_cons, List.map_cons, List.mapM_cons, hrest]
    rcases h c (by simp) with hc | hc
    · have hnil : c = [] := List.eq_nil_of_length_eq_zero hc
      simp [rlpChildSlot, hnil]
    · have hne : ¬ c = [] := by intro hn; rw [hn] at hc; simp at hc
      simp [rlpChildSlot, hne, hc]

/-- **The `mptNodeIs → MutableNode` round-trip** (bead `4ch8f.75.3`):
    every well-formed guest node's RLP decodes to exactly its
    abstraction. Combined with `mptNodeIs_wf` / `mptNodeIs`'s
    `bytesRegion ptr n.rlp`, the guest's node assertion determines the
    SpecRef `MutableNode` the `.29` walk relates to `trieLookup`. The
    proof cases are those of `mptNodeKindSpec_rlp`: the proven
    `decodeFully_encode` round-trip, then `hpDecode_hpEncode` for the
    leaf/extension paths and `mapM_rlpChildSlot` for the branch slots. -/
theorem rlpToMutableNode_rlp (n : MptNode) (hwf : n.WF) :
    rlpToMutableNode n.rlp = some (alpha_node n) := by
  have hdec := decodeFully_encode n.rlpItem (n.rlp_length_lt hwf)
  unfold rlpToMutableNode
  rw [show n.rlp = encode n.rlpItem from rfl, hdec]
  cases n with
  | leaf p v =>
    obtain ⟨hp, -, -⟩ := hwf
    show (if 2 < ([RLPItem.bytes (hpEncode true p), RLPItem.bytes v]).length
      then _ else
        match hpDecode (hpEncode true p) with
        | some (true, nibs) => some (MutableNode.leaf nibs v)
        | some (false, nibs) => some (MutableNode.extension nibs (.hashed v))
        | none => none) = some (MutableNode.leaf p v)
    rw [if_neg (by simp), hpDecode_hpEncode true p hp]
  | extension p c =>
    obtain ⟨hp, -, -⟩ := hwf
    show (if 2 < ([RLPItem.bytes (hpEncode false p), RLPItem.bytes c]).length
      then _ else
        match hpDecode (hpEncode false p) with
        | some (true, nibs) => some (MutableNode.leaf nibs c)
        | some (false, nibs) => some (MutableNode.extension nibs (.hashed c))
        | none => none) = some (MutableNode.extension p (.hashed c))
    rw [if_neg (by simp), hpDecode_hpEncode false p hp]
  | branch cs v =>
    obtain ⟨hcs, hcl, -⟩ := hwf
    have hlen : (cs.map RLPItem.bytes ++ [RLPItem.bytes v]).length = 17 := by
      simp [hcs]
    have htake : (cs.map RLPItem.bytes ++ [RLPItem.bytes v]).take 16 =
        cs.map RLPItem.bytes :=
      List.take_left' (by simp [hcs])
    have hgetD : (cs.map RLPItem.bytes ++ [RLPItem.bytes v]).getD 16 (.bytes []) =
        RLPItem.bytes v := by
      have h16 : (cs.map RLPItem.bytes).length = 16 := by simp [hcs]
      rw [List.getD, List.getElem?_append_right (by omega), h16]
      rfl
    show (if 2 < (cs.map RLPItem.bytes ++ [RLPItem.bytes v]).length then
        if (cs.map RLPItem.bytes ++ [RLPItem.bytes v]).length = 17 then
          match ((cs.map RLPItem.bytes ++ [RLPItem.bytes v]).take 16).mapM rlpChildSlot,
              (cs.map RLPItem.bytes ++ [RLPItem.bytes v]).getD 16 (.bytes []) with
          | some children, .bytes v => some (MutableNode.branch children v)
          | _, _ => none
        else none
      else _) = _
    rw [if_pos (by rw [hlen]; omega), if_pos hlen, htake, hgetD,
        mapM_rlpChildSlot cs hcl]
    rfl

/-! ## Pure hop (obligation #10 / #11799)

One step of `mpt_walk` replaces the current node ref by the **Resolve**
of a taken child hash (not a cursor advance inside the parent RLP). SpecRef
`trieLookupAux` takes the same step once the hashed placeholder has been
substituted by the resolved child `MutableNode`. The three lemmas below
are the pure content of that hop; the machine triple re-establishes
`mptNodeIs` on the replacement bytes and advances the path suffix.

**Domain gate (named, not silent):** `MptNode` v1 / `alpha_node` admit
hash-or-empty children only. Inlined sub-32-byte children (`mpt_branch_child`
status 2 / guest path that adds the child offset into the parent buffer)
are **excluded by this gate**, not merely unhandled — a future reader must
not treat them as a hole inside the proven domain. `n.WF` already enforces
extension child length = 32 and branch slots empty-or-32.

Resolve on the pure side is `nodeDbLookupSpec` (coherent with
`build_node_db` by `nodeDbLookupSpec_eq_build_node_db`); the decoded child
is `alpha_node child` via `rlpToMutableNode_rlp`. -/

open Stateless.SpecRef (trieLookupAux keccak256 keyToNibbles)

/-- Spec hop through an extension whose child is already a deep
    `MutableNode` (prefix matches). Definitional unfolding of
    `trieLookupAux` — the shape the guest hop re-establishes after
    Resolve substitutes the hashed placeholder. -/
theorem trieLookupAux_extension_hop
    (f : Nat) (seg : List (BitVec 8)) (child : MutableNode)
    (nibbles : List (BitVec 8)) (pos : Nat)
    (h_prefix : (nibbles.drop pos).take seg.length = seg) :
    trieLookupAux (f + 1) (some (.extension seg child)) nibbles pos =
      trieLookupAux f (some child) nibbles (pos + seg.length) := by
  simp [trieLookupAux, h_prefix]

/-- Spec hop through a branch whose chosen child slot is already a deep
    `MutableNode` (path still has a residual nibble). -/
theorem trieLookupAux_branch_hop
    (f : Nat) (children : List (Option MutableNode)) (value : List (BitVec 8))
    (nibbles : List (BitVec 8)) (pos : Nat) (child : MutableNode)
    (h_more : pos < nibbles.length)
    (h_slot : children.getD (nibbles.getD pos 0).toNat none = some child) :
    trieLookupAux (f + 1) (some (.branch children value)) nibbles pos =
      trieLookupAux f (some child) nibbles (pos + 1) := by
  have hle : ¬ nibbles.length ≤ pos := Nat.not_le_of_gt h_more
  -- `simp` unfolds `getD` on both sides; rewrite the slot first.
  simp only [trieLookupAux, hle, ite_false]
  -- Goal: trieLookupAux f (children.getD idx none) ... = trieLookupAux f (some child) ...
  simpa using congrArg (fun c => trieLookupAux f c nibbles (pos + 1)) h_slot

/-- Shallow abstraction of a well-formed extension is the SpecRef
    extension with a `.hashed` placeholder for the child. -/
theorem alpha_node_extension (p c : List (BitVec 8)) :
    alpha_node (.extension p c) = .extension p (.hashed c) := rfl

/-- Shallow abstraction of a well-formed branch maps empty slots to
    `none` and 32-byte hash slots to `some (.hashed _)`. -/
theorem alpha_node_branch (cs : List (List (BitVec 8))) (v : List (BitVec 8)) :
    alpha_node (.branch cs v) =
      .branch (cs.map fun c => if c = [] then none else some (.hashed c)) v := rfl

/-- **Extension hop (pure).** Guest is at well-formed extension `n`, path
    prefix matches, Resolve answers with well-formed child `child`. Spec
    hop after substituting `alpha_node child` for the `.hashed` placeholder
    equals one `trieLookupAux` step onto that child; decode of the resolved
    RLP is exactly `alpha_node child`.

    Material facts discharged here: path suffix advances by `path.length`;
    Resolve coherence (`nodeDbLookupSpec`); shallow alpha of parent; alpha
    of child. The machine triple additionally re-establishes `mptNodeIs`
    on the replacement bytes (node-ref REPLACEMENT, not cursor advance). -/
theorem mpt_walk_hop_extension
    (path childHash : List (BitVec 8)) (child : MptNode)
    (nodes : List (List (BitVec 8)))
    (nibbles : List (BitVec 8)) (pos f : Nat)
    (_hwf_ext : (MptNode.extension path childHash).WF)
    (hwf_child : child.WF)
    (_hlookup : nodeDbLookupSpec nodes childHash = some child.rlp)
    (h_prefix : (nibbles.drop pos).take path.length = path) :
    alpha_node (.extension path childHash) =
        .extension path (.hashed childHash) ∧
      rlpToMutableNode child.rlp = some (alpha_node child) ∧
      trieLookupAux (f + 1)
          (some (.extension path (alpha_node child))) nibbles pos =
        trieLookupAux f (some (alpha_node child))
          nibbles (pos + path.length) := by
  refine ⟨rfl, rlpToMutableNode_rlp child hwf_child, ?_⟩
  exact trieLookupAux_extension_hop f path (alpha_node child) nibbles pos h_prefix

/-- **Branch hop (pure).** Guest is at well-formed branch `n`, residual
    path nibble selects a **32-byte hash** slot (empty and inlined sub-32
    slots are outside this theorem — empty is a terminal miss handled
    separately; inlined is excluded by the domain gate). Resolve answers
    with well-formed child `child`. Spec hop after substituting
    `alpha_node child` at that slot equals one `trieLookupAux` step. -/
theorem mpt_walk_hop_branch
    (cs : List (List (BitVec 8))) (value childHash : List (BitVec 8))
    (child : MptNode) (nodes : List (List (BitVec 8)))
    (nibbles : List (BitVec 8)) (pos f : Nat)
    (hwf_br : (MptNode.branch cs value).WF)
    (hwf_child : child.WF)
    (h_more : pos < nibbles.length)
    (h_idx_bound : (nibbles.getD pos 0).toNat < cs.length)
    (h_slot : cs.getD (nibbles.getD pos 0).toNat [] = childHash)
    (h_hash : childHash.length = 32)
    (_hlookup : nodeDbLookupSpec nodes childHash = some child.rlp) :
    let idx := (nibbles.getD pos 0).toNat
    let children := cs.map fun c =>
      if c = [] then none else some (MutableNode.hashed c)
    let children' := children.set idx (some (alpha_node child))
    rlpToMutableNode child.rlp = some (alpha_node child) ∧
      children.getD idx none = some (.hashed childHash) ∧
      trieLookupAux (f + 1) (some (.branch children' value)) nibbles pos =
        trieLookupAux f (some (alpha_node child)) nibbles (pos + 1) := by
  intro idx children children'
  have hdec := rlpToMutableNode_rlp child hwf_child
  have hne : childHash ≠ [] := by
    intro heq; rw [heq] at h_hash; cases h_hash
  have hget : children.getD idx none = some (.hashed childHash) := by
    have hlt : idx < cs.length := h_idx_bound
    -- map getD via getElem
    have hidx : cs[idx] = childHash := by
      have : cs.getD idx [] = childHash := h_slot
      rwa [List.getElem_eq_getD (fallback := ([] : List (BitVec 8)))]
    simp only [children, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hlt, Option.map_some, Option.getD_some, hidx,
      if_neg hne]
  have hset : children'.getD idx none = some (alpha_node child) := by
    have hlt : idx < children.length := by
      simpa [children, List.length_map] using h_idx_bound
    simp only [children', List.getD_eq_getElem?_getD]
    rw [List.getElem?_set_self hlt]
    rfl
  let _ := hwf_br
  refine ⟨hdec, hget, ?_⟩
  exact trieLookupAux_branch_hop f children' value nibbles pos (alpha_node child)
    h_more hset

/-- Resolve miss is out of the hop: `nodeDbLookupSpec` returning `none`
    means the guest fails the walk (no replacement node). Recorded so the
    machine triple's fail arm has a pure counterpart. -/
theorem mpt_walk_hop_resolve_miss
    (childHash : List (BitVec 8)) (nodes : List (List (BitVec 8)))
    (hmiss : nodeDbLookupSpec nodes childHash = none) :
    ¬ ∃ (child : MptNode), nodeDbLookupSpec nodes childHash = some child.rlp := by
  intro ⟨_, h⟩
  rw [hmiss] at h
  cases h

/-! ### coverRef — two-node hop (anti-vacuity)

A 1-node leaf trie satisfies the gate but never **hops**. The cover
instance below is an extension whose child is a 32-byte hash Resolve'd
from a one-entry node DB to a leaf — so the hop lemmas' Resolve+prefix
hypotheses are inhabited and the walk takes a real extension step. -/

/-- Concrete two-node cover: extension `[0x0A] → leaf [0x0B]↦[0x99]`. -/
def mptWalkHopCoverLeaf : MptNode := .leaf [0x0B] [0x99]

def mptWalkHopCoverLeafHash : List (BitVec 8) :=
  keccak256 mptWalkHopCoverLeaf.rlp

def mptWalkHopCoverExt : MptNode :=
  .extension [0x0A] mptWalkHopCoverLeafHash

def mptWalkHopCoverNodes : List (List (BitVec 8)) :=
  [mptWalkHopCoverLeaf.rlp]

theorem mptWalkHopCoverLeaf_wf : mptWalkHopCoverLeaf.WF := by
  refine ⟨fun n hn => ?_, by decide, by decide⟩
  fin_cases hn; decide

theorem mptWalkHopCoverExt_wf : mptWalkHopCoverExt.WF := by
  refine ⟨fun n hn => ?_, by decide, ?_⟩
  · fin_cases hn; decide
  · simpa [mptWalkHopCoverExt, mptWalkHopCoverLeafHash] using
      Stateless.SpecRef.keccak256_length mptWalkHopCoverLeaf.rlp

/-- Resolve on the cover instance returns the leaf RLP. -/
theorem mptWalkHopCover_lookup :
    nodeDbLookupSpec mptWalkHopCoverNodes mptWalkHopCoverLeafHash =
      some mptWalkHopCoverLeaf.rlp := by
  simp [nodeDbLookupSpec, mptWalkHopCoverNodes, mptWalkHopCoverLeafHash]

/-- **coverRef** for the hop domain: a two-node extension→leaf instance
    inhabiting every hypothesis of `mpt_walk_hop_extension`, including a
    real hop (path length 1, Resolve hit). A 1-node leaf alone would
    satisfy WF without exercising the hop. -/
theorem mpt_walk_hop_precondition_reachable :
    ∃ (path childHash : List (BitVec 8)) (child : MptNode)
      (nodes : List (List (BitVec 8))) (nibbles : List (BitVec 8))
      (pos : Nat),
      (MptNode.extension path childHash).WF ∧
      child.WF ∧
      nodeDbLookupSpec nodes childHash = some child.rlp ∧
      (nibbles.drop pos).take path.length = path ∧
      0 < path.length :=
  ⟨[0x0A], mptWalkHopCoverLeafHash, mptWalkHopCoverLeaf,
    mptWalkHopCoverNodes, [0x0A, 0x0B], 0,
    mptWalkHopCoverExt_wf, mptWalkHopCoverLeaf_wf,
    mptWalkHopCover_lookup, rfl, Nat.zero_lt_one⟩

/-! ## Executable cross-checks (anti-vacuity)

The same concrete vectors `MptAssertions` exercises `mptNodeKindSpec`
on, decoded all the way to the `MutableNode`, plus an end-to-end
`trieLookup` read over a decoded 1-node trie (mirroring the
`WitnessState.lean` `trieLookup` `#guard`s). -/

#guard match rlpToMutableNode (MptNode.leaf [1, 2, 3] [0xaa]).rlp with
  | some (.leaf [1, 2, 3] [0xaa]) => true | _ => false

#guard match rlpToMutableNode (MptNode.extension [5] (List.replicate 32 0)).rlp with
  | some (.extension [5] (.hashed h)) => h == List.replicate 32 0 | _ => false

-- A branch with one hash-referenced child (slot 3) and a value: empty
-- slots decode to `none`, the 32-byte ref to `.hashed`.
#guard
  let childHash : List (BitVec 8) := List.replicate 32 0x42
  let cs := (List.range 16).map (fun i => if i == 3 then childHash else [])
  match rlpToMutableNode (MptNode.branch cs [0x99]).rlp with
  | some (.branch children [0x99]) =>
      children.length == 16
      && (children.getD 3 none matches some (.hashed _))
      && ((List.range 16).all fun i => i == 3 || (children.getD i (some (.hashed [])) matches none))
  | _ => false

-- Non-nodes fail to decode.
#guard rlpToMutableNode [] matches none
#guard rlpToMutableNode (EvmAsm.EL.RLP.encode (.bytes [0x01])) matches none

-- End-to-end: a 1-node trie whose leaf holds all the nibbles of key
-- 0xAB — SpecRef `trieLookup` over the DECODED guest node finds the
-- value, and a mismatching key reads `none`.
#guard
  let key : List (BitVec 8) := [0xAB]
  let leaf := MptNode.leaf (Stateless.SpecRef.keyToNibbles key) [0x99]
  (match Stateless.SpecRef.trieLookup (rlpToMutableNode leaf.rlp) key with
   | .ok (some [0x99]) => true | _ => false)
  && (match Stateless.SpecRef.trieLookup (rlpToMutableNode leaf.rlp) [0xAC] with
      | .ok none => true | _ => false)

-- Two-node hop cover: Resolve hits, extension prefix matches, and
-- trieLookupAux after substituting the resolved leaf returns the value.
-- This is the anti-vacuity check that a 1-node leaf cannot provide.
#guard
  let leaf := mptWalkHopCoverLeaf
  let h := mptWalkHopCoverLeafHash
  let nodes := mptWalkHopCoverNodes
  let nibbles : List (BitVec 8) := [0x0A, 0x0B]
  nodeDbLookupSpec nodes h == some leaf.rlp
  && (match trieLookupAux 3 (some (.extension [0x0A] (alpha_node leaf)))
        nibbles 0 with
      | .ok (some [0x99]) => true | _ => false)
  && (match trieLookupAux 3 (some (alpha_node leaf)) nibbles 1 with
      | .ok (some [0x99]) => true | _ => false)

-- The round-trip theorem is non-vacuous: a concrete WF witness.
example : (MptNode.leaf [1, 2, 3] [0xaa]).WF := by
  refine ⟨fun n hn => ?_, by decide, by decide⟩
  fin_cases hn <;> decide

end EvmAsm.Evm64
