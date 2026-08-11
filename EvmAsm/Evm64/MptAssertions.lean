/-
  EvmAsm.Evm64.MptAssertions

  Separation-logic assertions for the guest's MPT node structures: the
  RLP node shapes the MPT walkers parse, and the appended node DB the
  MPT-set write path builds.

  ## Layout faithfulness — what the guest ACTUALLY keeps

  **Note**: the scheme-A anchor `NODE_DB_BUCKETS = 0xa0130000` (4 MiB) was
  deleted (GH #11995) — it was *aspirational*: no emitted guest instruction
  ever referenced it, and the `Stateless/Witness/NodeDb/*` scaffold modules
  it anchored are removed (GH #11994). The real node
  structures, which this module describes, are:

  1. **Raw RLP nodes** — the MPT routines all consume RLP-encoded node
     byte strings in place and return `(ptr, len)` views or small copies:
     * `mpt_node_kind` (`EvmAsm/Codegen/Programs/Mpt.lean:139`, guest
       `0x8000417c`): classifies a node as 0 branch / 1 extension /
       2 leaf / 3 fail. Discriminator: RLP list item 2 **exists** ⇒
       branch (it does not count to 17); otherwise the high nibble of
       the first byte of item 0 — hex-prefix flags 0/1 ⇒ extension,
       2/3 ⇒ leaf, else fail.
     * `mpt_branch_child` (`Mpt.lean:283`, `0x80004240`): nibble-indexed
       child slot — RLP item `nibble`; length 32 ⇒ hash copied out,
       0 ⇒ empty, else inlined node.
     * `mpt_leaf_extract` / `mpt_extension_extract`
       (`EvmAsm/Codegen/Programs/MptInternal.lean:553/768`,
       `0x800078b0`/`0x80006a38`): unpack the hex-prefix compact path of
       item 0 into a caller nibble buffer and return item 1
       (value / child ref) as an absolute `(ptr, len)` into the node RLP.
     * `mpt_node_slot_encode` (`EvmAsm/Codegen/Programs/MptEncode.lean:523`,
       `0x80004db0`): child slot bytes for a parent — the RLP verbatim if
       `< 32` bytes, else `0xa0 ++ keccak256(node)`.

     `MptNode` below is the decoded view of those three shapes;
     `MptNode.rlp` is the byte string the routines consume, and
     `mptNodeKindSpec` mirrors `mpt_node_kind`'s actual discriminator.

  2. **The appended node DB** (`EvmAsm/Codegen/Programs/MptSetAcc.lean`,
     the `mset_db_*` `.data` structure): a bump-arena record log holding
     re-encoded nodes produced by the MPT-set write path.
     * `node_db_append` (`MptSetAcc.lean:58`, guest `0x80006120`):
       keccaks the node, writes the record
       `hash[32] | len:u64 LE | bytes[len] zero-padded to 8` at
       `*mset_db_top`, bumps `top` by `40 + ((len+7) &&& ~7)` and
       `*mset_db_count` by one. No capacity guard — bounded only by the
       8 MiB slab (`mset_db_data`, `.zero 8388608`,
       `MptSetAcc.lean:998`).
     * `node_db_lookup` (`MptSetAcc.lean:139`, `0x800061e0`): linear
       scan over `count` records comparing the full 32-byte hash (four
       u64 loads); hit returns the absolute node ptr `record+40` and
       the stored length.
     `nodeDbIs` below is that record log; `nodeDbLookupSpec` is the
     scan's semantic model, tied to the spec-reference
     `SpecRef.build_node_db` (the port of `witness_state.py`).

  3. **The resolve cache** (`mpt_node_resolve` `MptSetAcc.lean:242`
     `0x80006288`, reset by `mpt_resolve_cache_reset` `:199`
     `0x80006264`): a direct-mapped 4096-slot cache, index = low 12 bits
     of the target hash's first two bytes (little-endian), entries
     `hash[32] | absPtr:u64 | len:u64` (48 B) at
     `mset_res_cache_data + 48*idx`, valid flags (u64) at
     `mset_res_cache_valid + 8*idx`. Resolve order: appended DB →
     cache → `witness_lookup_by_hash` (cache filled only on witness
     hits).

  ## Static sizing

  The append arena is a **fixed 8 MiB `.data` slab**
  (`NODE_DB_DATA_BYTES`); the number of re-encoded nodes a block can
  produce is bounded by the ~200 Mgas block gas limit (every trie write
  is paid for), so the fixed slab covers valid executions. The resolve
  cache is fixed 4096 × 48 B + 4096 × 8 B. The `.data` symbol addresses
  (`mset_db_data = 0xa3c9ba80` etc. in the current build, per
  `EvmAsm/Codegen/GuestAddrs.lean`) are link-layout-dependent, so the
  assertions are parametrized by the base/cell addresses; the constants
  here carry only the fixed *sizes*.

  ## Faithfulness ties in this module

  * `mptNodeKindSpec_rlp`: the spec mirror of `mpt_node_kind`'s
    discriminator classifies every well-formed `MptNode.rlp` as its
    constructor's tag (via the proven RLP `decodeFully_encode`
    round-trip) — plus executable `#guard`s on concrete branch /
    extension / leaf byte vectors.
  * `hpDecode_hpEncode`: the hex-prefix path decode
    (`mpt_leaf_extract`'s nibble unpacking) round-trips.
  * `nodeDbLookupSpec_eq_build_node_db`: the linear-scan model equals
    lookup in the spec-reference `build_node_db` association list.
  * `nodeDbIs_snoc`: appending a record lands it exactly at
    `base + nodeDbSize nodes` — the address `node_db_append` computes —
    and `roundUp8_eq_alignToDword` pins the stride arithmetic to the
    routine's `(len+7) &&& ~7` mask.
  * An `LBU` example consuming a `nodeDbIs` record through the proven
    `bytesRegion_lbu_within` triple.

  The MPT routines have no functional `cpsTripleWithin` specs yet (only
  byte-identity drift guards); this module fixes the vocabulary those
  specs will be stated in.
-/

import EvmAsm.Evm64.StateAssertions
import EvmAsm.Stateless.SpecRef.WitnessState
import EvmAsm.EL.RLP.Properties

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.EL.RLP

/-! ## Hex-prefix compact path encoding

Yellow-paper appendix C, exactly as `mpt_leaf_extract` /
`mpt_extension_extract` parse it (`MptInternal.lean:553/768`) and as
`mpt_node_kind` discriminates it (`Mpt.lean:119-138`): first byte's high
nibble = `2*isLeaf + parity`; odd paths carry their first nibble in the
low half of byte 0; remaining nibbles are packed two per byte, high
nibble first. -/

/-- Pack an even-length nibble list two-per-byte, high nibble first. -/
def hpPackPairs : List (BitVec 8) → List (BitVec 8)
  | a :: b :: rest => BitVec.ofNat 8 (a.toNat * 16 + b.toNat) :: hpPackPairs rest
  | _ => []

/-- Unpack packed nibble pairs (high nibble first). -/
def hpUnpackPairs (bs : List (BitVec 8)) : List (BitVec 8) :=
  bs.flatMap (fun b => [BitVec.ofNat 8 (b.toNat / 16), BitVec.ofNat 8 (b.toNat % 16)])

/-- Hex-prefix encode with an explicit flag nibble (0 = extension,
    2 = leaf): first byte's high nibble is `flag + parity`; odd paths
    carry their first nibble in the low half of byte 0. -/
def hpEncodeAux (flag : Nat) (nibbles : List (BitVec 8)) : List (BitVec 8) :=
  if nibbles.length % 2 = 1 then
    BitVec.ofNat 8 ((flag + 1) * 16 + (nibbles.headD 0).toNat) :: hpPackPairs nibbles.tail
  else
    BitVec.ofNat 8 (flag * 16) :: hpPackPairs nibbles

/-- Hex-prefix encode a nibble path (each element `< 16`). -/
def hpEncode (isLeaf : Bool) (nibbles : List (BitVec 8)) : List (BitVec 8) :=
  hpEncodeAux (if isLeaf then 2 else 0) nibbles

/-- Hex-prefix decode: the leaf flag and the nibble path. Mirrors the
    guest's parse: bit 1 of the head nibble is the leaf flag, bit 0 the
    parity, and **bits 2-3 are ignored** — the `% 4` is the spec's masking
    (`compact_to_nibbles`, `amsterdam/incremental_mpt.py:878-889`, ported at
    `SpecRef/IncrementalMpt.lean:76-86`, computes `first_nibble & 0x02` and
    `& 0x01` and never inspects the high two bits).  This decoder used to
    reject a head nibble `≥ 4`; GH #10528 removed that, so the guest is no
    longer stricter than the spec and a guest-equals-spec statement carries
    one fewer side-condition. -/
def hpDecode (bs : List (BitVec 8)) : Option (Bool × List (BitVec 8)) :=
  match bs with
  | [] => none
  | b0 :: rest =>
    match (b0.toNat / 16) % 4 with
    | 0 => some (false, hpUnpackPairs rest)
    | 1 => some (false, BitVec.ofNat 8 (b0.toNat % 16) :: hpUnpackPairs rest)
    | 2 => some (true, hpUnpackPairs rest)
    | _ => some (true, BitVec.ofNat 8 (b0.toNat % 16) :: hpUnpackPairs rest)

theorem hpDecode_cons_div0 (b0 : BitVec 8) (rest : List (BitVec 8))
    (h : b0.toNat / 16 % 4 = 0) :
    hpDecode (b0 :: rest) = some (false, hpUnpackPairs rest) := by
  show (match (b0.toNat / 16) % 4 with
    | 0 => some (false, hpUnpackPairs rest)
    | 1 => some (false, BitVec.ofNat 8 (b0.toNat % 16) :: hpUnpackPairs rest)
    | 2 => some (true, hpUnpackPairs rest)
    | _ => some (true, BitVec.ofNat 8 (b0.toNat % 16) :: hpUnpackPairs rest)) = _
  rw [h]

theorem hpDecode_cons_div1 (b0 : BitVec 8) (rest : List (BitVec 8))
    (h : b0.toNat / 16 % 4 = 1) :
    hpDecode (b0 :: rest) =
      some (false, BitVec.ofNat 8 (b0.toNat % 16) :: hpUnpackPairs rest) := by
  show (match (b0.toNat / 16) % 4 with
    | 0 => some (false, hpUnpackPairs rest)
    | 1 => some (false, BitVec.ofNat 8 (b0.toNat % 16) :: hpUnpackPairs rest)
    | 2 => some (true, hpUnpackPairs rest)
    | _ => some (true, BitVec.ofNat 8 (b0.toNat % 16) :: hpUnpackPairs rest)) = _
  rw [h]

theorem hpDecode_cons_div2 (b0 : BitVec 8) (rest : List (BitVec 8))
    (h : b0.toNat / 16 % 4 = 2) :
    hpDecode (b0 :: rest) = some (true, hpUnpackPairs rest) := by
  show (match (b0.toNat / 16) % 4 with
    | 0 => some (false, hpUnpackPairs rest)
    | 1 => some (false, BitVec.ofNat 8 (b0.toNat % 16) :: hpUnpackPairs rest)
    | 2 => some (true, hpUnpackPairs rest)
    | _ => some (true, BitVec.ofNat 8 (b0.toNat % 16) :: hpUnpackPairs rest)) = _
  rw [h]

theorem hpDecode_cons_div3 (b0 : BitVec 8) (rest : List (BitVec 8))
    (h : b0.toNat / 16 % 4 = 3) :
    hpDecode (b0 :: rest) =
      some (true, BitVec.ofNat 8 (b0.toNat % 16) :: hpUnpackPairs rest) := by
  show (match (b0.toNat / 16) % 4 with
    | 0 => some (false, hpUnpackPairs rest)
    | 1 => some (false, BitVec.ofNat 8 (b0.toNat % 16) :: hpUnpackPairs rest)
    | 2 => some (true, hpUnpackPairs rest)
    | _ => some (true, BitVec.ofNat 8 (b0.toNat % 16) :: hpUnpackPairs rest)) = _
  rw [h]

theorem hpUnpackPairs_hpPackPairs : ∀ (nibs : List (BitVec 8)),
    (∀ n ∈ nibs, n.toNat < 16) → nibs.length % 2 = 0 →
    hpUnpackPairs (hpPackPairs nibs) = nibs
  | [], _, _ => rfl
  | [_], _, heven => by simp at heven
  | a :: b :: rest, hn, heven => by
    have ha : a.toNat < 16 := hn a (by simp)
    have hb : b.toNat < 16 := hn b (by simp)
    have ih := hpUnpackPairs_hpPackPairs rest (fun n hm => hn n (by simp [hm]))
      (by simp only [List.length_cons] at heven ⊢; omega)
    show hpUnpackPairs (BitVec.ofNat 8 (a.toNat * 16 + b.toNat) :: hpPackPairs rest) = _
    unfold hpUnpackPairs
    rw [List.flatMap_cons]
    have htoNat : (BitVec.ofNat 8 (a.toNat * 16 + b.toNat)).toNat =
        a.toNat * 16 + b.toNat := by
      rw [BitVec.toNat_ofNat]
      omega
    have hdiv : (BitVec.ofNat 8 (a.toNat * 16 + b.toNat)).toNat / 16 = a.toNat := by
      rw [htoNat]; omega
    have hmod : (BitVec.ofNat 8 (a.toNat * 16 + b.toNat)).toNat % 16 = b.toNat := by
      rw [htoNat]; omega
    rw [hdiv, hmod, BitVec.ofNat_toNat, BitVec.ofNat_toNat,
        BitVec.setWidth_eq, BitVec.setWidth_eq]
    show a :: b :: hpUnpackPairs (hpPackPairs rest) = a :: b :: rest
    rw [ih]

/-- Round trip at a fixed flag nibble. -/
theorem hpDecode_hpEncodeAux_ext (nibs : List (BitVec 8))
    (hn : ∀ n ∈ nibs, n.toNat < 16) :
    hpDecode (hpEncodeAux 0 nibs) = some (false, nibs) := by
  unfold hpEncodeAux
  by_cases hodd : nibs.length % 2 = 1
  · rw [if_pos hodd]
    cases nibs with
    | nil => simp at hodd
    | cons n0 rest =>
      have hn0 : n0.toNat < 16 := hn n0 (by simp)
      simp only [List.headD_cons, List.tail_cons]
      have htoNat : (BitVec.ofNat 8 ((0 + 1) * 16 + n0.toNat)).toNat =
          16 + n0.toNat := by
        rw [BitVec.toNat_ofNat]
        omega
      rw [hpDecode_cons_div1 _ _ (by rw [htoNat]; omega)]
      have hmod : (BitVec.ofNat 8 ((0 + 1) * 16 + n0.toNat)).toNat % 16 = n0.toNat := by
        rw [htoNat]; omega
      rw [hmod, BitVec.ofNat_toNat, BitVec.setWidth_eq,
          hpUnpackPairs_hpPackPairs rest (fun n hm => hn n (by simp [hm]))
            (by simp only [List.length_cons] at hodd ⊢; omega)]
  · rw [if_neg hodd]
    have hdiv : (BitVec.ofNat 8 (0 * 16)).toNat / 16 = 0 := by decide
    rw [hpDecode_cons_div0 _ _ (by omega),
        hpUnpackPairs_hpPackPairs nibs hn (by omega)]

/-- Round trip at the leaf flag. -/
theorem hpDecode_hpEncodeAux_leaf (nibs : List (BitVec 8))
    (hn : ∀ n ∈ nibs, n.toNat < 16) :
    hpDecode (hpEncodeAux 2 nibs) = some (true, nibs) := by
  unfold hpEncodeAux
  by_cases hodd : nibs.length % 2 = 1
  · rw [if_pos hodd]
    cases nibs with
    | nil => simp at hodd
    | cons n0 rest =>
      have hn0 : n0.toNat < 16 := hn n0 (by simp)
      simp only [List.headD_cons, List.tail_cons]
      have htoNat : (BitVec.ofNat 8 ((2 + 1) * 16 + n0.toNat)).toNat =
          48 + n0.toNat := by
        rw [BitVec.toNat_ofNat]
        omega
      rw [hpDecode_cons_div3 _ _ (by rw [htoNat]; omega)]
      have hmod : (BitVec.ofNat 8 ((2 + 1) * 16 + n0.toNat)).toNat % 16 = n0.toNat := by
        rw [htoNat]; omega
      rw [hmod, BitVec.ofNat_toNat, BitVec.setWidth_eq,
          hpUnpackPairs_hpPackPairs rest (fun n hm => hn n (by simp [hm]))
            (by simp only [List.length_cons] at hodd ⊢; omega)]
  · rw [if_neg hodd]
    have hdiv : (BitVec.ofNat 8 (2 * 16)).toNat / 16 = 2 := by decide
    rw [hpDecode_cons_div2 _ _ (by omega),
        hpUnpackPairs_hpPackPairs nibs hn (by omega)]

/-- **Hex-prefix round-trip** — the faithfulness tie for the path
    unpacking done by `mpt_leaf_extract` / `mpt_extension_extract`. -/
theorem hpDecode_hpEncode (isLeaf : Bool) (nibs : List (BitVec 8))
    (hn : ∀ n ∈ nibs, n.toNat < 16) :
    hpDecode (hpEncode isLeaf nibs) = some (isLeaf, nibs) := by
  cases isLeaf with
  | false => exact hpDecode_hpEncodeAux_ext nibs hn
  | true => exact hpDecode_hpEncodeAux_leaf nibs hn

/-- The head byte of a hex-prefix encoding carries `flag + parity` in its
    high nibble — the discriminator `mpt_node_kind` reads. -/
theorem hpEncodeAux_head_div (flag : Nat) (hflag : flag ≤ 2)
    (nibs : List (BitVec 8)) (hn : ∀ n ∈ nibs, n.toNat < 16) :
    ∃ b0 tl, hpEncodeAux flag nibs = b0 :: tl ∧
      b0.toNat / 16 = flag + nibs.length % 2 := by
  unfold hpEncodeAux
  by_cases hodd : nibs.length % 2 = 1
  · rw [if_pos hodd]
    refine ⟨_, _, rfl, ?_⟩
    have hn0 : (nibs.headD 0).toNat < 16 := by
      cases nibs with
      | nil => simp at hodd
      | cons a r => exact hn a (by simp)
    rw [BitVec.toNat_ofNat, hodd]
    omega
  · rw [if_neg hodd]
    refine ⟨_, _, rfl, ?_⟩
    rw [BitVec.toNat_ofNat, show nibs.length % 2 = 0 from by omega]
    omega

/-! ## MPT node shapes -/

/-- The three RLP MPT node shapes the guest routines parse. Children of a
    branch and the extension child are **hash references** (empty or
    32-byte keccak strings) in this vocabulary — the `< 32`-byte inlined
    child form (`mpt_branch_child` status 2) is left to a follow-up. -/
inductive MptNode where
  | leaf (path : List (BitVec 8)) (value : List (BitVec 8))
  | extension (path : List (BitVec 8)) (childHash : List (BitVec 8))
  | branch (children : List (List (BitVec 8))) (value : List (BitVec 8))
  deriving Repr, BEq

namespace MptNode

/-- Well-formedness, matching what the guest parsers accept/produce:
    paths are nibble lists (each `< 16`, ≤ 64 nibbles = one keccak of
    depth), extension children are exactly 32-byte hashes, branch nodes
    have exactly 16 children each empty-or-32-byte. The value cap (16 MiB)
    is generous — trie values are RLP accounts (~111 B) / storage words
    (≤ 33 B) — and is used only for the RLP decode-length bound. -/
def WF : MptNode → Prop
  | .leaf p v => (∀ n ∈ p, n.toNat < 16) ∧ p.length ≤ 64 ∧ v.length ≤ 0x1000000
  | .extension p c => (∀ n ∈ p, n.toNat < 16) ∧ p.length ≤ 64 ∧ c.length = 32
  | .branch cs v => cs.length = 16 ∧ (∀ c ∈ cs, c.length = 0 ∨ c.length = 32) ∧
      v.length ≤ 0x1000000

/-- The node as a spec-level RLP item. -/
def rlpItem : MptNode → RLPItem
  | .leaf p v => .list [.bytes (hpEncode true p), .bytes v]
  | .extension p c => .list [.bytes (hpEncode false p), .bytes c]
  | .branch cs v => .list (cs.map .bytes ++ [.bytes v])

/-- The RLP-encoded node — the byte string every MPT guest routine
    consumes. -/
def rlp (n : MptNode) : List (BitVec 8) := encode n.rlpItem

/-- The tag `mpt_node_kind` returns for this shape. -/
def kindTag : MptNode → Nat
  | .branch .. => 0
  | .extension .. => 1
  | .leaf .. => 2

end MptNode

/-- Spec mirror of `mpt_node_kind` (`Mpt.lean:139`): item 2 exists ⇒
    branch (the routine probes `rlp_list_nth_item(node, 2)`, it does not
    count to 17); otherwise a 2-item list whose item 0 is a byte string
    is discriminated by the high nibble of its first byte. Everything
    else is a parse failure (3). Domain note: on a 2-item list whose
    item 0 is a *nested list*, the routine peeks the raw sub-encoding
    while this mirror returns 3 — such shapes are not well-formed trie
    nodes and outside `MptNode`. -/
def mptNodeKindSpec (node : List (BitVec 8)) : Nat :=
  match decodeFully node with
  | some (.list items) =>
    if 2 < items.length then 0
    else
      match items with
      | [.bytes path, _] =>
        match path with
        | [] => 3
        | b0 :: _ =>
          let hn := b0.toNat / 16
          if hn < 2 then 1 else if hn < 4 then 2 else 3
      | _ => 3
  | _ => 3

/-! ### RLP length bound (for the decode round-trip) -/

/-- `encodeBytes` adds at most 9 prefix bytes. -/
theorem encodeBytes_length_le (data : List (BitVec 8))
    (h : data.length < 256 ^ 8) :
    (encodeBytes data).length ≤ data.length + 9 := by
  match data with
  | [b] => by_cases hb : b.toNat < 0x80 <;> simp [encodeBytes, hb]
  | [] => simp [encodeBytes]
  | b1 :: b2 :: tl =>
    simp only [encodeBytes]
    by_cases hshort : (b1 :: b2 :: tl).length ≤ 55
    · rw [if_pos (by simpa using hshort)]
      simp
    · rw [if_neg (by simpa using hshort)]
      have hlb : (Nat.toBytesBE (b1 :: b2 :: tl).length).length ≤ 8 :=
        Nat.toBytesBE_length_le _ 8 (by exact_mod_cast h)
      simp only [List.length_append, List.length_cons, List.length_nil]
      simp at hlb ⊢
      omega

/-- `encodeItems` over byte-string items distributes lengths. -/
theorem encodeItems_bytes_length_le (items : List (List (BitVec 8)))
    (bound : Nat) (h : ∀ b ∈ items, (encodeBytes b).length ≤ bound) :
    (encode.encodeItems (items.map .bytes)).length ≤ items.length * bound := by
  induction items with
  | nil => simp [encode.encodeItems]
  | cons x xs ih =>
    show (encode (.bytes x) ++ encode.encodeItems (xs.map .bytes)).length ≤ _
    rw [List.length_append]
    have h1 : (encode (RLPItem.bytes x)).length ≤ bound := h x (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    simp only [List.length_cons]
    rw [Nat.succ_mul]
    omega

/-- Packed pairs never exceed the nibble count. -/
theorem hpPackPairs_length_le : ∀ (nibs : List (BitVec 8)),
    (hpPackPairs nibs).length ≤ nibs.length
  | [] => by simp [hpPackPairs]
  | [_] => by simp [hpPackPairs]
  | _ :: _ :: rest => by
    have := hpPackPairs_length_le rest
    simp only [hpPackPairs, List.length_cons]
    omega

theorem hpEncodeAux_length_le (flag : Nat) (nibs : List (BitVec 8)) :
    (hpEncodeAux flag nibs).length ≤ nibs.length + 1 := by
  unfold hpEncodeAux
  by_cases hodd : nibs.length % 2 = 1
  · rw [if_pos hodd]
    have h1 := hpPackPairs_length_le nibs.tail
    have h2 : nibs.tail.length ≤ nibs.length := by
      cases nibs <;> simp
    simp only [List.length_cons]
    omega
  · rw [if_neg hodd]
    have := hpPackPairs_length_le nibs
    simp only [List.length_cons]
    omega

theorem hpEncode_length_le (isLeaf : Bool) (nibs : List (BitVec 8)) :
    (hpEncode isLeaf nibs).length ≤ nibs.length + 1 :=
  hpEncodeAux_length_le _ nibs

/-- Every well-formed node's RLP is far below the full-decode bound. -/
theorem MptNode.rlp_length_lt (n : MptNode) (hwf : n.WF) :
    n.rlp.length < 256 ^ 8 := by
  cases n with
  | leaf p v =>
    obtain ⟨hp, hplen, hvlen⟩ := hwf
    have hpath := hpEncode_length_le true p
    have h1 : (encode (RLPItem.bytes (hpEncode true p))).length ≤
        (hpEncode true p).length + 9 :=
      encodeBytes_length_le (hpEncode true p) (by omega)
    have h2 : (encode (RLPItem.bytes v)).length ≤ v.length + 9 :=
      encodeBytes_length_le v (by omega)
    have hpay : (encode.encodeItems
        [RLPItem.bytes (hpEncode true p), RLPItem.bytes v]).length ≤
        (hpEncode true p).length + 9 + (v.length + 9) := by
      show ((encode (.bytes (hpEncode true p))) ++
        ((encode (.bytes v)) ++ [])).length ≤ _
      simp only [List.length_append, List.length_nil]
      omega
    show (encode (.list [.bytes (hpEncode true p), .bytes v])).length < 256 ^ 8
    unfold encode
    dsimp only
    by_cases hshort : (encode.encodeItems
        [RLPItem.bytes (hpEncode true p), RLPItem.bytes v]).length ≤ 55
    · rw [if_pos hshort]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · rw [if_neg hshort]
      have hlb := Nat.toBytesBE_length_le
        (encode.encodeItems
          [RLPItem.bytes (hpEncode true p), RLPItem.bytes v]).length 8
        (by omega)
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  | extension p c =>
    obtain ⟨hp, hplen, hclen⟩ := hwf
    have hpath := hpEncode_length_le false p
    have h1 : (encode (RLPItem.bytes (hpEncode false p))).length ≤
        (hpEncode false p).length + 9 :=
      encodeBytes_length_le (hpEncode false p) (by omega)
    have h2 : (encode (RLPItem.bytes c)).length ≤ c.length + 9 :=
      encodeBytes_length_le c (by omega)
    have hpay : (encode.encodeItems
        [RLPItem.bytes (hpEncode false p), RLPItem.bytes c]).length ≤
        (hpEncode false p).length + 9 + (c.length + 9) := by
      show ((encode (.bytes (hpEncode false p))) ++
        ((encode (.bytes c)) ++ [])).length ≤ _
      simp only [List.length_append, List.length_nil]
      omega
    show (encode (.list [.bytes (hpEncode false p), .bytes c])).length < 256 ^ 8
    unfold encode
    dsimp only
    by_cases hshort : (encode.encodeItems
        [RLPItem.bytes (hpEncode false p), RLPItem.bytes c]).length ≤ 55
    · rw [if_pos hshort]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · rw [if_neg hshort]
      have hlb := Nat.toBytesBE_length_le
        (encode.encodeItems
          [RLPItem.bytes (hpEncode false p), RLPItem.bytes c]).length 8
        (by omega)
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  | branch cs v =>
    obtain ⟨hcs, hcl, hvlen⟩ := hwf
    have hchild : ∀ b ∈ cs, (encodeBytes b).length ≤ 41 := by
      intro b hb
      have := encodeBytes_length_le b (by rcases hcl b hb with h | h <;> omega)
      rcases hcl b hb with h | h <;> omega
    have hchildren := encodeItems_bytes_length_le cs 41 hchild
    have hv : (encode (RLPItem.bytes v)).length ≤ v.length + 9 :=
      encodeBytes_length_le v (by omega)
    have happ : (encode.encodeItems (cs.map .bytes ++ [.bytes v])).length =
        (encode.encodeItems (cs.map .bytes)).length +
        (encode.encodeItems [.bytes v]).length := by
      clear hchildren hchild hcl hcs
      induction cs with
      | nil => simp [encode.encodeItems]
      | cons x xs ih =>
        show (encode (.bytes x) ++
          encode.encodeItems (xs.map .bytes ++ [.bytes v])).length = _
        rw [List.length_append, ih]
        show _ = (encode (.bytes x) ++ encode.encodeItems (xs.map .bytes)).length + _
        rw [List.length_append]
        omega
    have hval : (encode.encodeItems [RLPItem.bytes v]).length ≤ v.length + 9 := by
      show ((encode (.bytes v)) ++ []).length ≤ _
      simp only [List.length_append, List.length_nil]
      omega
    have hpay : (encode.encodeItems (cs.map .bytes ++ [.bytes v])).length ≤
        16 * 41 + (v.length + 9) := by
      rw [happ]
      rw [hcs] at hchildren
      omega
    show (encode (.list (cs.map .bytes ++ [.bytes v]))).length < 256 ^ 8
    unfold encode
    dsimp only
    by_cases hshort : (encode.encodeItems
        (cs.map RLPItem.bytes ++ [RLPItem.bytes v])).length ≤ 55
    · rw [if_pos hshort]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · rw [if_neg hshort]
      have hlb := Nat.toBytesBE_length_le
        (encode.encodeItems (cs.map RLPItem.bytes ++ [RLPItem.bytes v])).length 8
        (by omega)
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-! ### Kind classification — the `mpt_node_kind` faithfulness tie -/

/-- **The spec mirror classifies every well-formed node as its shape's
    tag** — `mptNodeKindSpec n.rlp = n.kindTag`. This pins `MptNode.rlp`
    to the exact discriminator the guest routine implements (item-2
    presence for branch, hex-prefix high nibble for extension/leaf). -/
theorem mptNodeKindSpec_rlp (n : MptNode) (hwf : n.WF) :
    mptNodeKindSpec n.rlp = n.kindTag := by
  have hdec := decodeFully_encode n.rlpItem (n.rlp_length_lt hwf)
  unfold mptNodeKindSpec
  rw [show n.rlp = encode n.rlpItem from rfl, hdec]
  cases n with
  | branch cs v =>
    obtain ⟨hcs, -, -⟩ := hwf
    show (if 2 < (cs.map RLPItem.bytes ++ [RLPItem.bytes v]).length then (0 : Nat)
      else _) = 0
    rw [if_pos (by simp [hcs])]
  | leaf p v =>
    obtain ⟨hp, -, -⟩ := hwf
    obtain ⟨b0, tl, heq, hdiv⟩ := hpEncodeAux_head_div 2 (by omega) p hp
    show (if 2 < ([RLPItem.bytes (hpEncode true p), RLPItem.bytes v]).length
      then (0 : Nat)
      else match hpEncode true p with
        | [] => 3
        | b0 :: _ =>
          if b0.toNat / 16 < 2 then 1 else if b0.toNat / 16 < 4 then 2 else 3) = 2
    rw [if_neg (by simp)]
    rw [show hpEncode true p = hpEncodeAux 2 p from rfl, heq]
    show (if b0.toNat / 16 < 2 then (1 : Nat)
      else if b0.toNat / 16 < 4 then 2 else 3) = 2
    have hmod2 : p.length % 2 < 2 := Nat.mod_lt _ (by decide)
    rw [if_neg (by omega), if_pos (by omega)]
  | extension p c =>
    obtain ⟨hp, -, -⟩ := hwf
    obtain ⟨b0, tl, heq, hdiv⟩ := hpEncodeAux_head_div 0 (by omega) p hp
    show (if 2 < ([RLPItem.bytes (hpEncode false p), RLPItem.bytes c]).length
      then (0 : Nat)
      else match hpEncode false p with
        | [] => 3
        | b0 :: _ =>
          if b0.toNat / 16 < 2 then 1 else if b0.toNat / 16 < 4 then 2 else 3) = 1
    rw [if_neg (by simp)]
    rw [show hpEncode false p = hpEncodeAux 0 p from rfl, heq]
    show (if b0.toNat / 16 < 2 then (1 : Nat)
      else if b0.toNat / 16 < 4 then 2 else 3) = 1
    have hmod2 : p.length % 2 < 2 := Nat.mod_lt _ (by decide)
    rw [if_pos (by omega)]

/-- Branch child projection: the decoded items of a branch node are its
    child refs (as byte strings) followed by the value — the structure
    `mpt_branch_child`'s `rlp_list_nth_item(node, nibble)` indexes. -/
theorem decodeFully_branch_rlp (cs : List (List (BitVec 8))) (v : List (BitVec 8))
    (hwf : (MptNode.branch cs v).WF) :
    decodeFully (MptNode.branch cs v).rlp =
      some (.list (cs.map .bytes ++ [.bytes v])) :=
  decodeFully_encode _ ((MptNode.branch cs v).rlp_length_lt hwf)

/-- Leaf projection: the decoded items are the compact path and value —
    what `mpt_leaf_extract` unpacks (path → nibbles via `hpDecode`,
    value returned as a view). -/
theorem decodeFully_leaf_rlp (p v : List (BitVec 8))
    (hwf : (MptNode.leaf p v).WF) :
    decodeFully (MptNode.leaf p v).rlp =
      some (.list [.bytes (hpEncode true p), .bytes v]) :=
  decodeFully_encode _ ((MptNode.leaf p v).rlp_length_lt hwf)

/-- Extension projection (`mpt_extension_extract`). -/
theorem decodeFully_extension_rlp (p c : List (BitVec 8))
    (hwf : (MptNode.extension p c).WF) :
    decodeFully (MptNode.extension p c).rlp =
      some (.list [.bytes (hpEncode false p), .bytes c]) :=
  decodeFully_encode _ ((MptNode.extension p c).rlp_length_lt hwf)

/-! ### The node assertion -/

/-- `mptNodeIs ptr n` — ownership of one RLP-encoded MPT node at
    (dword-aligned) `ptr`, with the shape's well-formedness. This is the
    resource `mpt_node_kind` / `mpt_branch_child` / `mpt_leaf_extract` /
    `mpt_extension_extract` / `mpt_node_slot_encode` read. -/
def mptNodeIs (ptr : Word) (n : MptNode) : Assertion :=
  fun ps => n.WF ∧ bytesRegion ptr n.rlp ps

theorem mptNodeIs_eq_bytesRegion {ptr : Word} {n : MptNode} (hwf : n.WF) :
    mptNodeIs ptr n = bytesRegion ptr n.rlp := by
  funext ps
  exact propext ⟨fun h => h.2, fun h => ⟨hwf, h⟩⟩

theorem mptNodeIs_wf {ptr : Word} {n : MptNode} {ps : PartialState}
    (h : mptNodeIs ptr n ps) : n.WF := h.1

theorem pcFree_mptNodeIs {ptr : Word} {n : MptNode} : (mptNodeIs ptr n).pcFree :=
  fun ps h => bytesRegion_pcFree ptr n.rlp ps h.2

instance (ptr : Word) (n : MptNode) : Assertion.PCFree (mptNodeIs ptr n) :=
  ⟨pcFree_mptNodeIs⟩

-- Concrete cross-checks of the kind discriminator (executable, mirrors
-- the `mpt_node_kind` contract on real byte vectors).
#guard mptNodeKindSpec (MptNode.branch (List.replicate 16 []) []).rlp = 0
#guard mptNodeKindSpec (MptNode.leaf [1, 2, 3] [0xaa]).rlp = 2
#guard mptNodeKindSpec (MptNode.extension [5] (List.replicate 32 0)).rlp = 1
#guard mptNodeKindSpec [] = 3
-- Path round-trip on an odd and an even path.
#guard hpDecode (hpEncode true [1, 2, 3]) = some (true, [1, 2, 3])
#guard hpDecode (hpEncode false [0xa, 0xb]) = some (false, [0xa, 0xb])

/-! ## The appended node DB (`mset_db_*`) -/

/-- The append arena is a fixed 8 MiB `.data` slab (`mset_db_data`,
    `.zero 8388608`, `MptSetAcc.lean:998`). -/
def NODE_DB_DATA_BYTES : Nat := 0x800000

/-- Round up to the next dword, as `node_db_append`'s
    `(len + 7) &&& ~7` computes. -/
def roundUp8 (n : Nat) : Nat := 8 * ((n + 7) / 8)

/-- The stride arithmetic matches the routine's mask instruction
    sequence: `roundUp8 len` is `(len + 7) &&& ~7` (i.e. `alignToDword`
    of the u64 `len + 7`). -/
theorem roundUp8_eq_alignToDword (len : Nat) (h : len + 7 < 2 ^ 64) :
    BitVec.ofNat 64 (roundUp8 len) = alignToDword (BitVec.ofNat 64 (len + 7)) := by
  have halign : (0 : Word).toNat % 8 = 0 := by decide
  have := alignToDword_add_ofNat_of_aligned (base := (0 : Word)) (i := len + 7)
    halign (by simp; omega)
  rw [show (0 : Word) + BitVec.ofNat 64 (len + 7) = BitVec.ofNat 64 (len + 7) from by
        bv_omega,
      show (0 : Word) + BitVec.ofNat 64 (8 * ((len + 7) / 8)) =
        BitVec.ofNat 64 (8 * ((len + 7) / 8)) from by bv_omega] at this
  rw [show roundUp8 len = 8 * ((len + 7) / 8) from rfl, ← this]

/-- One node-DB record, exactly as `node_db_append` writes it
    (`MptSetAcc.lean:58-100`): the 32-byte keccak of the node, the
    length as a little-endian u64, then the node bytes zero-padded to a
    dword boundary. -/
def nodeDbRecordBytes (node : List (BitVec 8)) : List (BitVec 8) :=
  Stateless.SpecRef.keccak256 node ++ Stateless.SpecRef.natToBytesLE 8 node.length ++
  node ++ List.replicate (roundUp8 node.length - node.length) 0

/-- Record stride: `40 + roundUp8 len` — the exact bump
    `node_db_append` applies to `mset_db_top`. -/
def nodeDbStride (node : List (BitVec 8)) : Nat := 40 + roundUp8 node.length

theorem nodeDbRecordBytes_length (node : List (BitVec 8))
    (hk : (Stateless.SpecRef.keccak256 node).length = 32) :
    (nodeDbRecordBytes node).length = nodeDbStride node := by
  unfold nodeDbRecordBytes nodeDbStride
  simp only [List.length_append, List.length_replicate, hk,
    Stateless.SpecRef.natToBytesLE, List.length_map, List.length_range]
  unfold roundUp8
  omega

/-- Total byte size of a record log — the `mset_db_top - mset_db_data`
    the guest maintains. -/
def nodeDbSize (nodes : List (List (BitVec 8))) : Nat :=
  nodes.foldr (fun n acc => nodeDbStride n + acc) 0

@[simp] theorem nodeDbSize_nil : nodeDbSize [] = 0 := rfl

theorem nodeDbSize_cons (n : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    nodeDbSize (n :: rest) = nodeDbStride n + nodeDbSize rest := rfl

/-- `nodeDbIs base nodes` — the appended node DB: the records of `nodes`
    (in append order) packed back-to-back from `base`
    (`mset_db_data`; link-layout-dependent, so parametrized). -/
def nodeDbIs (base : Word) (nodes : List (List (BitVec 8))) : Assertion :=
  match nodes with
  | [] => empAssertion
  | n :: rest =>
      bytesRegion base (nodeDbRecordBytes n) **
      nodeDbIs (base + BitVec.ofNat 64 (nodeDbStride n)) rest

/-- The record-count cell (`mset_db_count`). -/
def nodeDbCountIs (countLoc : Word) (nodes : List (List (BitVec 8))) : Assertion :=
  countLoc ↦ₘ BitVec.ofNat 64 nodes.length

/-- The bump-pointer cell (`mset_db_top`): always `base + nodeDbSize`. -/
def nodeDbTopIs (topLoc base : Word) (nodes : List (List (BitVec 8))) : Assertion :=
  topLoc ↦ₘ (base + BitVec.ofNat 64 (nodeDbSize nodes))

theorem nodeDbIs_nil {base : Word} : nodeDbIs base [] = empAssertion := rfl

theorem nodeDbIs_cons {base : Word} {n : List (BitVec 8)}
    {rest : List (List (BitVec 8))} :
    nodeDbIs base (n :: rest) =
      (bytesRegion base (nodeDbRecordBytes n) **
       nodeDbIs (base + BitVec.ofNat 64 (nodeDbStride n)) rest) := rfl

theorem pcFree_nodeDbIs {base : Word} {nodes : List (List (BitVec 8))} :
    (nodeDbIs base nodes).pcFree := by
  induction nodes generalizing base with
  | nil => exact pcFree_emp
  | cons _ _ ih => exact pcFree_sepConj (bytesRegion_pcFree _ _) ih

instance (base : Word) (nodes : List (List (BitVec 8))) :
    Assertion.PCFree (nodeDbIs base nodes) := ⟨pcFree_nodeDbIs⟩

instance (countLoc : Word) (nodes : List (List (BitVec 8))) :
    Assertion.PCFree (nodeDbCountIs countLoc nodes) := ⟨pcFree_memIs⟩

instance (topLoc base : Word) (nodes : List (List (BitVec 8))) :
    Assertion.PCFree (nodeDbTopIs topLoc base nodes) := ⟨pcFree_memIs⟩

/-- Split the record log: records of `xs ++ ys` are the records of `xs`
    from `base` and those of `ys` from `base + nodeDbSize xs`. The scan
    and append lemmas both come from this. -/
theorem nodeDbIs_append (base : Word) (xs ys : List (List (BitVec 8))) :
    nodeDbIs base (xs ++ ys) =
      (nodeDbIs base xs ** nodeDbIs (base + BitVec.ofNat 64 (nodeDbSize xs)) ys) := by
  induction xs generalizing base with
  | nil =>
    simp only [List.nil_append, nodeDbIs_nil, sepConj_emp_left', nodeDbSize_nil]
    rw [show (BitVec.ofNat 64 0 : Word) = 0 from rfl,
        show base + (0 : Word) = base from by bv_omega]
  | cons n rest ih =>
    simp only [List.cons_append, nodeDbIs_cons, nodeDbSize_cons]
    rw [ih (base + BitVec.ofNat 64 (nodeDbStride n)), add_ofNat_add_ofNat,
        sepConj_assoc']

/-- **The `node_db_append` shape**: appending one node places its record
    exactly at `base + nodeDbSize nodes` — the address the routine
    computes from `mset_db_top` — leaving the earlier records untouched. -/
theorem nodeDbIs_snoc {base : Word} {nodes : List (List (BitVec 8))}
    {n : List (BitVec 8)} :
    nodeDbIs base (nodes ++ [n]) =
      (nodeDbIs base nodes **
       bytesRegion (base + BitVec.ofNat 64 (nodeDbSize nodes)) (nodeDbRecordBytes n)) := by
  rw [nodeDbIs_append]
  congr 1
  rw [nodeDbIs_cons, nodeDbIs_nil, sepConj_emp_right']

/-! ### The lookup model -/

/-- Semantic model of `node_db_lookup`'s linear scan
    (`MptSetAcc.lean:139-168`): the first record whose stored keccak
    equals the target hash. -/
def nodeDbLookupSpec (nodes : List (List (BitVec 8))) (h : List (BitVec 8)) :
    Option (List (BitVec 8)) :=
  nodes.find? (fun n => Stateless.SpecRef.keccak256 n == h)

theorem nodeDbLookupSpec_correct {nodes : List (List (BitVec 8))}
    {h n : List (BitVec 8)} (hf : nodeDbLookupSpec nodes h = some n) :
    n ∈ nodes ∧ Stateless.SpecRef.keccak256 n = h := by
  refine ⟨List.mem_of_find?_eq_some hf, ?_⟩
  have := List.find?_some hf
  simpa using this

/-- **Lookup-by-hash finds the appended node** — the scan model agrees
    with lookup in the spec-reference `build_node_db` association list
    (`SpecRef/WitnessState.lean`, the port of `witness_state.py`'s
    `Dict[keccak256(entry), entry]`). -/
theorem nodeDbLookupSpec_eq_build_node_db (nodes : List (List (BitVec 8)))
    (h : List (BitVec 8)) :
    nodeDbLookupSpec nodes h =
      (Stateless.SpecRef.build_node_db nodes).lookup h := by
  induction nodes with
  | nil => rfl
  | cons n rest ih =>
    show (n :: rest).find? _ = ((Stateless.SpecRef.keccak256 n, n) ::
      Stateless.SpecRef.build_node_db rest).lookup h
    rw [List.find?_cons, List.lookup_cons]
    by_cases hk : Stateless.SpecRef.keccak256 n = h
    · rw [show (Stateless.SpecRef.keccak256 n == h) = true from by simp [hk],
          show (h == Stateless.SpecRef.keccak256 n) = true from by simp [hk]]
    · rw [show (Stateless.SpecRef.keccak256 n == h) = false from by simp [hk],
          show (h == Stateless.SpecRef.keccak256 n) = false from by
            simp only [beq_eq_false_iff_ne, ne_eq]
            exact fun h' => hk h'.symm]
      exact ih

-- Executable cross-check: the scan finds an appended node by its hash.
#guard nodeDbLookupSpec [[0x01], [0x02, 0x03]]
  (Stateless.SpecRef.keccak256 [0x02, 0x03]) = some [0x02, 0x03]

/-! ### The resolve cache (`mset_res_cache_*`) -/

/-- 4096 direct-mapped slots (`mset_res_cache_valid` is
    `.zero 32768` = 4096 u64 flags; `mset_res_cache_data` is
    `.zero 196608` = 4096 × 48-byte entries, `MptSetAcc.lean:230-234`). -/
def RESOLVE_CACHE_SLOTS : Nat := 4096

/-- Entry stride: `hash[32] | absPtr:u64 | len:u64`. -/
def RESOLVE_CACHE_ENTRY_BYTES : Nat := 48

#guard RESOLVE_CACHE_SLOTS * RESOLVE_CACHE_ENTRY_BYTES = 196608
#guard RESOLVE_CACHE_SLOTS * 8 = 32768

/-- The slot index `mpt_node_resolve` computes
    (`MptSetAcc.lean:260-266`): the low 12 bits of the hash's first two
    bytes, little-endian (`hash[0] | hash[1] << 8`, masked `0xFFF`). -/
def resolveCacheIndexSpec (h : List (BitVec 8)) : Nat :=
  ((h.getD 0 0).toNat + 256 * (h.getD 1 0).toNat) % 4096

theorem resolveCacheIndexSpec_lt (h : List (BitVec 8)) :
    resolveCacheIndexSpec h < RESOLVE_CACHE_SLOTS :=
  Nat.mod_lt _ (by decide)

/-- One cache entry: the 48 bytes at `dataBase + 48*idx`. -/
def resolveCacheEntryIs (dataBase : Word) (idx : Nat)
    (hash : List (BitVec 8)) (absPtr len : Word) : Assertion :=
  fun ps => hash.length = 32 ∧
    bytesRegion (dataBase + BitVec.ofNat 64 (RESOLVE_CACHE_ENTRY_BYTES * idx))
      (hash ++ Stateless.SpecRef.natToBytesLE 8 absPtr.toNat ++
       Stateless.SpecRef.natToBytesLE 8 len.toNat) ps

/-- The slot's valid flag (u64 at `validBase + 8*idx`). -/
def resolveCacheValidIs (validBase : Word) (idx : Nat) (flag : Word) : Assertion :=
  (validBase + BitVec.ofNat 64 (8 * idx)) ↦ₘ flag

theorem pcFree_resolveCacheEntryIs {dataBase : Word} {idx : Nat}
    {hash : List (BitVec 8)} {absPtr len : Word} :
    (resolveCacheEntryIs dataBase idx hash absPtr len).pcFree :=
  fun ps h => bytesRegion_pcFree _ _ ps h.2

instance (dataBase : Word) (idx : Nat) (hash : List (BitVec 8)) (absPtr len : Word) :
    Assertion.PCFree (resolveCacheEntryIs dataBase idx hash absPtr len) :=
  ⟨pcFree_resolveCacheEntryIs⟩

instance (validBase : Word) (idx : Nat) (flag : Word) :
    Assertion.PCFree (resolveCacheValidIs validBase idx flag) := ⟨pcFree_memIs⟩

/-- In-range slots stay inside the fixed cache arena. -/
theorem resolveCacheEntry_in_arena {idx : Nat} (hidx : idx < RESOLVE_CACHE_SLOTS) :
    RESOLVE_CACHE_ENTRY_BYTES * idx + RESOLVE_CACHE_ENTRY_BYTES ≤ 196608 := by
  rw [show RESOLVE_CACHE_ENTRY_BYTES = 48 from rfl]
  rw [show RESOLVE_CACHE_SLOTS = 4096 from rfl] at hidx
  omega

/-! ### Machine-level tie-in

The byte-read primitive over a node-DB record, restated against
`nodeDbIs`'s head record: reading byte `i` of the record region yields
`(nodeDbRecordBytes n)[i]`. Consumes the proven `bytesRegion_lbu_within`
(the record's hash-compare loads and the returned node bytes both live
in this region). -/

example (rd rs1 : Reg) (base ptr vOld : Word) (n : List (BitVec 8))
    (rest : List (List (BitVec 8))) (i : Nat) (hrd : rd ≠ .x0)
    (halign : ptr.toNat % 8 = 0) (hi : i < (nodeDbRecordBytes n).length)
    (hover : ptr.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (ptr + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU rd rs1 0))
      ((rs1 ↦ᵣ (ptr + BitVec.ofNat 64 i)) ** (rd ↦ᵣ vOld) **
       nodeDbIs ptr (n :: rest))
      ((rs1 ↦ᵣ (ptr + BitVec.ofNat 64 i)) **
       (rd ↦ᵣ (((nodeDbRecordBytes n)[i]'hi).zeroExtend 64)) **
       nodeDbIs ptr (n :: rest)) := by
  rw [nodeDbIs_cons]
  have hcore := bytesRegion_lbu_within rd rs1 ptr vOld base
    (nodeDbRecordBytes n) i hrd halign hi hover hvalid
  have hframed := cpsTripleWithin_frameR
    (nodeDbIs (ptr + BitVec.ofNat 64 (nodeDbStride n)) rest) pcFree_nodeDbIs hcore
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    hframed

end EvmAsm.Evm64
