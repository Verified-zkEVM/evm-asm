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

-- The round-trip theorem is non-vacuous: a concrete WF witness.
example : (MptNode.leaf [1, 2, 3] [0xaa]).WF := by
  refine ⟨fun n hn => ?_, by decide, by decide⟩
  fin_cases hn <;> decide

end EvmAsm.Evm64
