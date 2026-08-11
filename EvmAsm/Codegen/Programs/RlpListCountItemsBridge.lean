/-
  EvmAsm.Codegen.Programs.RlpListCountItemsBridge

  GH #11341 — the fourth and last of that issue's bridges. The other three
  (`rlp_content_to_u256_be`, `rlp_bytes_encoded_size`, `rlp_list_encoded_size`) are
  already `.bridged`; `rlp_list_count_items` is the one still on `.machineOnly`, and
  it is the largest of the four rather than a fourth mechanical repeat.

  ## What is being bridged, and why the row needs it

  `rlp_list_count_items_spec_within`'s post is `Result bytes base listLen status result`,
  whose success case is

      Success bytes base listLen count :=
        ∃ cursorOff endPtr,
          StrictListPayload bytes base listLen cursorOff endPtr ∧
          StrictPrefix bytes base endPtr cursorOff count listLen

  Every predicate there is LOCAL: `StrictPrefix` (RlpListNthItemSAsmBase:312) is a
  second, independent copy of the walk relation, and nothing tied it to the shared
  model. So the theorem says the routine matches *our restatement* of RLP, and a
  transcription slip in that restatement is invisible — the proof still closes and
  the differential still passes elsewhere. That is exactly #11341's complaint.

  The shared-model side is `EvmAsm.Rv64.RLP.DecodeChain` (WalkDecodeBridge:412),
  which is phrased over `decodeAux` and already composes to a full `decodeItems` run
  via `decodeItems_of_chain` (general over `List RLPItem`, not arity-limited).

  ## ⭐ THREE MISMATCHES, and this file's strategy

  1. **Per-item translation.** `rlpItemDecode` (WalkNext:3649) is a five-disjunct
     `BitVec`-level relation (`BitVec.ult` comparisons); `decodeAux` is `Nat`-level.
  2. **Direction.** `StrictPrefix` grows by SNOC (`succ` extends at the far end);
     `DecodeChain` grows by CONS. Same shape as the `nibblePrefix`-vs-`flatMap`
     mismatch #11422 had to resolve with its own induction.
  3. **Items are not carried.** `StrictPrefix` tracks only a COUNT, so the bridge has
     to produce the `List RLPItem` existentially.

  STRATEGY: prove (2) and (3) FIRST, parameterised over (1) as a hypothesis. The
  structural induction is the part that can fail for interesting reasons; the
  per-item step is five mechanical disjuncts once the shape is known to work. Doing
  it in this order means a failure tells you something, and it isolates the
  remaining work to a single named obligation instead of leaving it entangled.

  ⚠️ STATUS: the structural half is proven here. The per-item translation
  (`RlpItemDecodeBridges`) is stated as an explicit hypothesis and is NOT yet
  discharged — see the note on `StrictPrefix.decodeChain_of_itemBridge`. No `sorry`
  is used: the unproven part is a hypothesis, so nothing here claims more than it
  has. Discharging it is what moves the registry row to `.bridged`.
-/

import EvmAsm.Codegen.Programs.RlpListCountItemsSAsmBase
import EvmAsm.Rv64.RLP.WalkDecodeBridge

namespace EvmAsm.Codegen.RlpListCountItemsBridge

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.EL.RLP
open EvmAsm.Codegen.RlpListNthItemSAsm (StrictPrefix)

/-- ⭐ **The per-item obligation**, isolated as a named predicate rather than left
    implicit in a proof.

    Says: whenever the machine relation `rlpItemDecode` accepts the item at byte
    offset `off`, the shared-model `decodeAux` decodes the same item there and
    advances to the same offset — at every fuel level (`∀ m`), which is the form
    `DecodeChain` consumes.

    ⚠️ This is the five-disjunct `BitVec`→`Nat` translation and is NOT proven yet.
    It is a hypothesis so that the structural result below is honest about what it
    depends on. `WalkDecodeBridge` already has the shape-specific pieces
    (`decodeAux_singleByte_bridge`, `decodeAux_shortBytes_bridge`,
    `decodeAux_bytes_all_fuel_of_decode`), so discharging this is assembling those
    plus the two list forms — not new mathematics. -/
def RlpItemDecodeBridges (bytes : List (BitVec 8)) (base endPtr : Word) : Prop :=
  ∀ (off : Nat) (next len : Word),
    rlpItemDecode bytes off (base + BitVec.ofNat 64 off) endPtr next len →
    ∃ item : RLPItem,
      ∀ m, decodeAux (m + 1) (bytes.drop off)
        = some (item, bytes.drop (next - base).toNat)


/-! ## Per-item translation, byte-string forms only (#11341 option 1)

    ⚠️ THE LIST FORMS CANNOT BE BRIDGED THIS WAY, which is why this section stops at
    byte strings. `rlpItemDecode`'s two list disjuncts require only that the item's
    SPAN FITS; `decodeAux` (Decode.lean:63) additionally decodes the payload
    (`decodeItems nDepth payload`, leftover must be empty) and returns `none` if it
    fails. So a list item with a malformed interior satisfies the machine relation and
    is REJECTED by the model — the implication is false on those disjuncts, not merely
    unproven.

    ⭐ The evidence was already in the tree: `WalkDecodeBridge` has
    `decodeAux_singleByte_*`, `_shortBytes_*`, `_bytes_*` and **no list bridge at
    all**. That absence is not an oversight; one cannot be written.

    Consequence: the guest walker accepts nested-list input the reference rejects,
    which against `decode_joined_encodings` is a LOOSER-than-reference shape. Whether
    that is reachable, and what verdict it deserves, is recorded on #11341 — it is a
    design question about what `rlp_walk_next` promises, not something to paper over
    here. This section proves what IS true. -/

/-- The single-byte range guard, read byte-exhaustively. `BitVec.ult` over a
    `zeroExtend`ed byte against a 64-bit literal is exactly the kind of mixed
    BitVec/Nat statement `omega` cannot see through, and it is decidable over 256
    cases — cheap, since the kernel's `Nat` is GMP-backed (CLAUDE.md). -/
private theorem lt_0x80_of_ult (b : BitVec 8)
    (h : BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true) : b.toNat < 0x80 := by
  revert b; decide

/-- Single-byte form: the machine disjunct's BitVec guards, translated to the Nat
    hypotheses `decodeAux_singleByte_bridge` already wants.

    All the decode content is in that existing lemma; this is purely the
    `BitVec`→`Nat` guard translation.

    ⭐ CURSOR ARITHMETIC IS A HYPOTHESIS (`hstep`), deliberately. Re-deriving
    `(next - base).toNat = off + 1` here would duplicate what the walk layer already
    proves (`StrictPrefix.step_bounds` and friends carry exactly these cursor facts),
    and it is not this lemma's job: this file translates DECODE relations, not pointer
    arithmetic. Keeping it out also stops an overflow side condition from leaking into
    every per-form lemma. -/
theorem decodeAux_of_singleByte
    {bytes : List (BitVec 8)} {base : Word} {off : Nat} {next : Word} {b : BitVec 8}
    (hget : bytes[off]? = some b)
    (hsmall : BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true)
    (hstep : (next - base).toNat = off + 1) :
    ∀ m, decodeAux (m + 1) (bytes.drop off)
      = some (.bytes [b], bytes.drop (next - base).toNat) := by
  intro m
  have hb : b.toNat < 0x80 := lt_0x80_of_ult b hsmall
  rw [hstep]
  exact decodeAux_singleByte_bridge bytes off b hget hb m

/-- The short-string range guards and the canonicality equivalence, read
    byte-exhaustively for the same reason as `lt_0x80_of_ult`. Bundled because they
    are all facts about the one prefix byte. -/
private theorem shortBytes_guards (b : BitVec 8)
    (hlo : ¬ BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true)
    (hhi : BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true) :
    0x80 ≤ b.toNat ∧ b.toNat ≤ 0xB7 ∧
      ((b.zeroExtend 64 - (0x80 : Word) = (1 : Word)) ↔ b.toNat - 0x80 = 1) := by
  revert b; decide

/-- The inner canonicality byte's guard: a length-1 short string's content byte must
    not be below 0x80 (else the single-byte form was required). -/
private theorem not_lt_0x80_of_not_ult (c : BitVec 8)
    (h : ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) : ¬ c.toNat < 0x80 := by
  revert c; decide

/-- Short-string form (`0x80 ≤ p < 0xb8`). Second of the three provable disjuncts.

    Same division of labour as the single-byte case: the decode content is already in
    `decodeAux_shortBytes_bridge`, so this translates the `BitVec` guards and takes
    the two facts that belong to other layers as hypotheses —
    `hstep` (cursor arithmetic, from the walk layer) and `hlen` (the region bound,
    from the ABI). Neither is a decode fact and re-deriving them here would couple
    this file to pointer and region reasoning it has no business doing. -/
theorem decodeAux_of_shortBytes
    {bytes : List (BitVec 8)} {base : Word} {off : Nat} {next : Word} {b : BitVec 8}
    (hget : bytes[off]? = some b)
    (hlo : ¬ BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true)
    (hhi : BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true)
    (hcanon : b.zeroExtend 64 - (0x80 : Word) = (1 : Word) →
      ∃ c : BitVec 8, bytes[off + 1]? = some c ∧
        ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true)
    (hlen : off + 1 + (b.toNat - 0x80) ≤ bytes.length)
    (hstep : (next - base).toNat = off + 1 + (b.toNat - 0x80)) :
    ∀ m, decodeAux (m + 1) (bytes.drop off)
      = some (.bytes ((bytes.drop (off + 1)).take (b.toNat - 0x80)),
          bytes.drop (next - base).toNat) := by
  intro m
  obtain ⟨hlo', hhi', hcanonIff⟩ := shortBytes_guards b hlo hhi
  have hcanon' : b.toNat - 0x80 = 1 →
      ∃ c : BitVec 8, bytes[off + 1]? = some c ∧ ¬ c.toNat < 0x80 := by
    intro h1
    obtain ⟨c, hc, hcnot⟩ := hcanon (hcanonIff.mpr h1)
    exact ⟨c, hc, not_lt_0x80_of_not_ult c hcnot⟩
  rw [hstep]
  exact decodeAux_shortBytes_bridge bytes off b hget hlo' hhi' hlen hcanon' m


/-! ## The restricted predicate, and a witness (#11694 review ask)

    ⛔ THIS IS NOT THE ROW'S BRIDGE and must not be mistaken for progress toward
    `.bridged`. `RlpItemDecodeBridges` — quantified over all five disjuncts — is
    UNSATISFIABLE on this routine's actual domain, because since #11675
    `rlp_list_count_items` is reached from `mpt_node_kind` and MPT branch children
    include INLINE EMBEDDED NODES, i.e. nested lists (`SpecRef/IncrementalMpt.lean:155`
    `resolveChildRefAux` has an explicit `| .list items =>` arm). A nested list's
    `decodeAux` is fuel-sensitive, so the `∀ m` link `DecodeChain` demands is false
    there — see #11711.

    What IS true, and what this section records, is the byte-string restriction. It is
    stated with the restriction VISIBLE in the predicate rather than hidden in a
    comment, so no caller can pick it up believing it covers lists. -/

/-- Per-item bridge restricted to byte-string prefix bytes (`p < 0xc0`).

    ⚠️ The `hbytes` guard is the whole point: it is what makes this provable, and it
    is what makes it insufficient for `rlp_list_count_items`. -/
def RlpItemDecodeBridgesBytes (bytes : List (BitVec 8)) (base endPtr : Word) : Prop :=
  ∀ (off : Nat) (next len : Word) (b : BitVec 8),
    bytes[off]? = some b →
    BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true →
    rlpItemDecode bytes off (base + BitVec.ofNat 64 off) endPtr next len →
    (next - base).toNat = off + 1 →
    ∃ item : RLPItem,
      ∀ m, decodeAux (m + 1) (bytes.drop off)
        = some (item, bytes.drop (next - base).toNat)

/-- ⭐ **Non-vacuity witness.** The single-byte form satisfies the restricted
    predicate's obligation, so the structural theorems are demonstrably about
    something rather than vacuously true.

    Deliberately stated for the sub-case that is *actually* dischargeable, rather than
    hand-picking an input to make the unrestricted predicate look inhabited — the
    latter would demonstrate the proposition is non-empty while saying nothing about
    the routine, which is the vacuity the review was guarding against. -/
theorem bridgesBytes_witness_singleByte
    {bytes : List (BitVec 8)} {base : Word} {off : Nat} {next : Word} {b : BitVec 8}
    (hget : bytes[off]? = some b)
    (hsmall : BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true)
    (hstep : (next - base).toNat = off + 1) :
    ∃ item : RLPItem,
      ∀ m, decodeAux (m + 1) (bytes.drop off)
        = some (item, bytes.drop (next - base).toNat) :=
  ⟨.bytes [b], decodeAux_of_singleByte hget hsmall hstep⟩

/-- ⭐ **The snoc lemma — mismatch (2) in one place.**

    `DecodeChain` is defined by recursion on the item list from the FRONT, so
    extending it at the BACK is not definitional. `StrictPrefix.succ` extends at the
    back, so this is the lemma that lets the machine relation's induction drive the
    model relation at all.

    Induction on `items`: the `nil` case turns `off = offMid` into a one-item chain,
    and the `cons` case simply threads the head decode through and recurses. Nothing
    deep — but it does not exist in `WalkDecodeBridge`, and without it the two
    relations cannot be related by induction in either direction. -/
theorem DecodeChain.snoc {bytes : List Byte} {item : RLPItem}
    {off offMid offEnd : Nat} :
    ∀ items : List RLPItem,
      DecodeChain bytes off items offMid →
      (∀ m, decodeAux (m + 1) (bytes.drop offMid) = some (item, bytes.drop offEnd)) →
      DecodeChain bytes off (items ++ [item]) offEnd := by
  intro items
  induction items generalizing off with
  | nil =>
    intro hchain hd
    -- `DecodeChain … [] offMid` is DEFINITIONALLY `off = offMid`, but it needs to be
    -- named as an `Eq` before `subst` will take it.
    have hoff : off = offMid := hchain
    subst hoff
    exact ⟨offEnd, hd, rfl⟩
  | cons i rest ih =>
    intro hchain hd
    obtain ⟨off1, hhead, htail⟩ := hchain
    exact ⟨off1, hhead, ih htail hd⟩

/-- ⭐ **The structural bridge** — mismatches (2) and (3) discharged.

    A machine-side `StrictPrefix` of length `count` yields a shared-model
    `DecodeChain` over *some* list of exactly `count` items, ending at the same
    offset. This is where the snoc-vs-cons reversal lives.

    Note the induction is on `StrictPrefix`, whose `succ` appends at the far end,
    while `DecodeChain` is defined by recursion on the item list from the front. The
    reconciliation is that `succ` extends the chain's TAIL, so the recursive call
    supplies `DecodeChain … items off` and the new item is appended — which is why
    the statement quantifies over the end offset rather than fixing it. -/
theorem StrictPrefix.decodeChain_of_itemBridge
    {bytes : List (BitVec 8)} {base endPtr : Word} {startOff count off : Nat}
    (hb : RlpItemDecodeBridges bytes base endPtr)
    (h : StrictPrefix bytes base endPtr startOff count off) :
    ∃ items : List RLPItem,
      items.length = count ∧ DecodeChain bytes startOff items off := by
  induction h with
  | zero => exact ⟨[], rfl, rfl⟩
  | succ count off next len hprefix hitem ih =>
    obtain ⟨items, hlen, hchain⟩ := ih
    obtain ⟨item, hdec⟩ := hb off next len hitem
    -- `items` walks startOff → off; the new item walks off → (next - base).
    -- Appending on the right is exactly `DecodeChain`'s composition, so this needs
    -- the snoc lemma below rather than a direct `cons`.
    refine ⟨items ++ [item], by simp [hlen], ?_⟩
    exact DecodeChain.snoc items hchain hdec

/-! ## Fuel-sensitive forms (GH #11795, on top of #11711)

    #11711 removed the fuel obstruction: `DecodeChainFrom` states a link at ONE
    budget rather than at every budget, so a nested list — whose `decodeAux` is
    fuel-sensitive — is now expressible as a link. This section carries the
    structural results above over to that predicate, which is the half of #11795
    that #11711 genuinely unblocks.

    ⚠️ **It is only half.** #11795 says that once `DecodeChain` stops demanding
    `∀ m`, discharging the per-item bridge "becomes assembling the existing pieces".
    That is not so, and the reason is worth stating precisely because the issue
    sequences work on it:

    `rlpItemDecode`'s two LIST disjuncts (`WalkNext.lean:3649`, the `0xc0`–`0xf7`
    and `≥ 0xf8` arms) require only header canonicality plus a **span fit** —
    `¬ ult (endPtr - cursor) span`. They say nothing about the payload. `decodeAux`
    (`Decode.lean:63`) additionally runs `decodeItems nDepth payload` and returns
    `none` unless it consumes the payload exactly. So a list item whose span fits
    but whose **interior is malformed** satisfies `rlpItemDecode` and is rejected by
    `decodeAux`, at every budget.

    ⇒ `RlpItemDecodeBridges`/`RlpItemDecodeBridgesFrom` remain unsatisfiable on the
    unrestricted domain for a reason INDEPENDENT of fuel. Fuel was one of two
    obstructions; #11711 closed that one. The residual is a genuine
    strength mismatch between the machine relation and the model, and it is named
    below as `RlpListInteriorsDecode` rather than left in prose — same discipline as
    `RlpItemDecodeBridgesBytes`'s visible `hbytes` guard. -/

/-- Per-item obligation in **fuel-sensitive** form: the model decode is exhibited at
    a single budget `floor` instead of at every budget.

    This is `RlpItemDecodeBridges` with #11711's fix applied. The `∀ m` in the
    original is what a nested list cannot satisfy; this form can express one. -/
def RlpItemDecodeBridgesFrom (bytes : List (BitVec 8)) (base endPtr : Word)
    (floor : Nat) : Prop :=
  ∀ (off : Nat) (next len : Word),
    rlpItemDecode bytes off (base + BitVec.ofNat 64 off) endPtr next len →
    ∃ item : RLPItem,
      decodeAux floor (bytes.drop off) = some (item, bytes.drop (next - base).toNat)

/-- The fuel-insensitive obligation implies the fuel-sensitive one at any positive
    budget — instantiate `∀ m` at `m := floor - 1`. Faithfulness: the new predicate
    asks for no more than the old one did. -/
theorem rlpItemDecodeBridgesFrom_of_bridges {bytes : List (BitVec 8)}
    {base endPtr : Word} {floor : Nat} (hfloor : 0 < floor)
    (hb : RlpItemDecodeBridges bytes base endPtr) :
    RlpItemDecodeBridgesFrom bytes base endPtr floor := by
  intro off next len hitem
  obtain ⟨item, hdec⟩ := hb off next len hitem
  refine ⟨item, ?_⟩
  obtain ⟨f, rfl⟩ : ∃ f, floor = f + 1 := ⟨floor - 1, by omega⟩
  exact hdec f

/-- `DecodeChainFrom`'s snoc lemma — the analogue of `DecodeChain.snoc`, needed for
    the same reason: `DecodeChainFrom` recurses on the item list from the FRONT
    while `StrictPrefix.succ` extends at the BACK. -/
theorem DecodeChainFrom.snoc {bytes : List Byte} {item : RLPItem} {floor : Nat}
    {off offMid offEnd : Nat} :
    ∀ items : List RLPItem,
      DecodeChainFrom bytes floor off items offMid →
      decodeAux floor (bytes.drop offMid) = some (item, bytes.drop offEnd) →
      DecodeChainFrom bytes floor off (items ++ [item]) offEnd := by
  intro items
  induction items generalizing off with
  | nil =>
    intro hchain hd
    have hoff : off = offMid := hchain
    subst hoff
    exact ⟨offEnd, hd, rfl⟩
  | cons i rest ih =>
    intro hchain hd
    obtain ⟨off1, hhead, htail⟩ := hchain
    exact ⟨off1, hhead, ih htail hd⟩

/-- ⭐ **The structural bridge, fuel-sensitive.** A machine-side `StrictPrefix` of
    length `count` yields a `DecodeChainFrom` over some list of exactly `count`
    items ending at the same offset.

    Same proof shape as `StrictPrefix.decodeChain_of_itemBridge`; the point is that
    its per-item hypothesis is now the satisfiable-in-principle
    `RlpItemDecodeBridgesFrom` rather than a predicate that is false on the live
    domain for fuel reasons. Composing this with `decodeItems_of_chainFrom` is what
    a `.bridged` regrade would consume. -/
theorem StrictPrefix.decodeChainFrom_of_itemBridge
    {bytes : List (BitVec 8)} {base endPtr : Word} {startOff count off floor : Nat}
    (hb : RlpItemDecodeBridgesFrom bytes base endPtr floor)
    (h : StrictPrefix bytes base endPtr startOff count off) :
    ∃ items : List RLPItem,
      items.length = count ∧ DecodeChainFrom bytes floor startOff items off := by
  induction h with
  | zero => exact ⟨[], rfl, rfl⟩
  | succ count off next len hprefix hitem ih =>
    obtain ⟨items, hlen, hchain⟩ := ih
    obtain ⟨item, hdec⟩ := hb off next len hitem
    refine ⟨items ++ [item], by simp [hlen], ?_⟩
    exact DecodeChainFrom.snoc items hchain hdec

/-- ⛔ **The residual obstruction, named.** `rlpItemDecode`'s list disjuncts check a
    span fit; `decodeAux` decodes the payload. This is the side condition that
    closes the difference: whenever the machine relation accepts a LIST item, the
    model actually decodes it at budget `floor`.

    Stated as its own predicate, with the list restriction visible, so that:

    * no caller can mistake `StrictPrefix.decodeChainFrom_of_itemBridge` for a
      complete bridge, and
    * the remaining work is one named obligation instead of prose in a docstring.

    ⚠️ This is NOT dischargeable from `rlpItemDecode` alone — it is strictly more
    information. Discharging it needs one of: a caller-side well-formedness fact
    (on the `mpt_node_kind` path the witness has already been validated, so the
    interiors *are* canonical — that is a precondition to import, not a theorem
    about this relation), or strengthening `rlpItemDecode`'s list arms to record
    what `rlp_walk_next_core` actually verifies after #11776. Choosing between those
    is a spec-shape decision for #11795, not something to settle silently here. -/
def RlpListInteriorsDecode (bytes : List (BitVec 8)) (base endPtr : Word)
    (floor : Nat) : Prop :=
  ∀ (off : Nat) (next len : Word) (b : BitVec 8),
    bytes[off]? = some b →
    ¬ BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true →
    rlpItemDecode bytes off (base + BitVec.ofNat 64 off) endPtr next len →
    ∃ inner : List RLPItem,
      decodeAux floor (bytes.drop off)
        = some (.list inner, bytes.drop (next - base).toNat)

/-- **The two halves compose.** Byte-string items (`p < 0xc0`) plus list items
    (`p ≥ 0xc0`) exhaust the prefix space, so the byte-string bridge and the list
    side condition together give the full per-item obligation.

    This is the honest shape of what #11795 asks for: the fuel obstruction is gone
    (#11711), the byte-string half is proven, and exactly one named hypothesis
    remains. It also shows the residual is not hiding additional fuel trouble —
    given `RlpListInteriorsDecode`, nothing further is needed. -/
theorem rlpItemDecodeBridgesFrom_of_parts {bytes : List (BitVec 8)}
    {base endPtr : Word} {floor : Nat}
    (hbytes : ∀ (off : Nat) (next len : Word) (b : BitVec 8),
      bytes[off]? = some b →
      BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true →
      rlpItemDecode bytes off (base + BitVec.ofNat 64 off) endPtr next len →
      ∃ item : RLPItem,
        decodeAux floor (bytes.drop off) = some (item, bytes.drop (next - base).toNat))
    (hlists : RlpListInteriorsDecode bytes base endPtr floor) :
    RlpItemDecodeBridgesFrom bytes base endPtr floor := by
  intro off next len hitem
  -- `rlpItemDecode` exposes the prefix byte, which is what splits the two cases.
  -- Destructure a COPY: both branches still need `hitem` itself.
  have hcopy := hitem
  obtain ⟨b, hget, _⟩ := hcopy
  by_cases hlt : BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true
  · exact hbytes off next len b hget hlt hitem
  · obtain ⟨inner, hdec⟩ := hlists off next len b hget hlt hitem
    exact ⟨.list inner, hdec⟩

/-! ## The additive strict relation (GH #11898, route 2 without touching 52 modules)

    #11795's residual is that `rlpItemDecode`'s two LIST arms require header canonicality
    plus a **span fit** and say nothing about the payload, while `decodeAux` additionally
    runs `decodeItems` and fails unless the payload is consumed exactly. So the machine
    relation is **weaker than the model on list interiors**, and no fuel work fixes that
    (#11711 closed the fuel half; this is the other one).

    #11898 enumerated the cost of the obvious repair: `rlpItemDecode` has **52 consuming
    modules**, and editing it in place risks the two determinism proofs
    (`RlpWalkDeterminism`, `WalkItemDeterminism`) where the relation being span-only may
    be load-bearing. @pirapira and I both read **route 2** — record what
    `rlp_walk_next_core` actually verifies, since after #11776 the routine does more than
    the relation admits — as the honest option, and a relation *weaker than the code* is
    the shape that lets a false-accept hide.

    ⭐ This is route 2 done **additively**, which is what makes it cheap: a new
    `rlpItemDecodeStrict` that conjoins the missing payload fact, an implication back to
    `rlpItemDecode` so **no existing consumer changes**, and the bridge discharge. The 52
    modules keep the weak relation; only the bridge consumes the strict one.

    ⚠️ What this does NOT do, and cannot: prove `rlp_walk_next` *satisfies* the strict
    relation. That is a routine-side obligation needing the walker's triple, and it is
    named below as `RlpWalkNextStrict` so the residual is one statement about the routine
    rather than a false claim about the model. That relocation is the whole point — before
    it, the gap looked like a model-side impossibility. -/

/-- `rlpItemDecode`, plus the fact its list arms omit: on a LIST prefix the payload
    actually decodes at budget `floor`, consuming exactly the item's span.

    Additive by construction — the first conjunct is the existing relation verbatim, so
    `rlpItemDecodeStrict_imp` below is immediate and every current consumer is unaffected. -/
def rlpItemDecodeStrict (bytes : List (BitVec 8)) (off : Nat)
    (cursor endPtr next len : Word) (nextOff floor : Nat) : Prop :=
  rlpItemDecode bytes off cursor endPtr next len
    ∧ (∀ b : BitVec 8, bytes[off]? = some b →
        ¬ BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true →
        ∃ inner : List RLPItem,
          decodeAux floor (bytes.drop off) = some (.list inner, bytes.drop nextOff))

/-- The strict relation implies the weak one, so **nothing that consumes
    `rlpItemDecode` needs to change**. This is the whole argument for the additive shape
    over an in-place edit of a relation with 52 consumers. -/
theorem rlpItemDecodeStrict_imp {bytes : List (BitVec 8)} {off : Nat}
    {cursor endPtr next len : Word} {nextOff floor : Nat}
    (h : rlpItemDecodeStrict bytes off cursor endPtr next len nextOff floor) :
    rlpItemDecode bytes off cursor endPtr next len := h.1

/-- ⭐ **The strict relation discharges the residual.** If every item the machine accepts
    satisfies the strict form, `RlpListInteriorsDecode` holds — so
    `rlpItemDecodeBridgesFrom_of_parts` closes and the per-item bridge is complete.

    That this is near-immediate is the POINT, not a weakness: it relocates the obligation
    from "prove something false about the model" to "prove the routine establishes what it
    already checks", which is the difference between a blocked issue and a scheduled one. -/
theorem rlpListInteriorsDecode_of_strict {bytes : List (BitVec 8)} {base endPtr : Word}
    {floor : Nat}
    (hstrict : ∀ (off : Nat) (next len : Word),
      rlpItemDecode bytes off (base + BitVec.ofNat 64 off) endPtr next len →
      rlpItemDecodeStrict bytes off (base + BitVec.ofNat 64 off) endPtr next len
        (next - base).toNat floor) :
    RlpListInteriorsDecode bytes base endPtr floor := by
  intro off next len b hget hlist hitem
  obtain ⟨_, hpay⟩ := hstrict off next len hitem
  exact hpay b hget hlist

/-- ⛔ **NOT a routine obligation — see `not_rlpWalkNextStrict_nestedNonCanonical`.**

    ⚠️ The docstring this declaration originally carried was WRONG, and the correction
    matters because #11795 schedules work against it. It claimed this was a statement
    about `rlp_walk_next` that *"after #11776 should be true"*, dischargeable by
    *"the walker's triple"*. Both halves are false:

    * **It contains no machine execution.** Its hypothesis is `rlpItemDecode`, a pure
      five-disjunct relation over `bytes` (`WalkNext.lean:3649`). So this is a property
      of the BYTE STRING, not of the routine, and no Hoare triple can discharge a goal
      the machine does not appear in.
    * **It is FALSE**, refuted below on the counterexample the tree already records at
      `ItemDecodeForward.lean:10-14`. `rlpItemDecode` accepts a list whose span fits and
      whose interior is malformed; `decodeAux` rejects it. That is precisely the gap
      `RlpListInteriorsDecode` (`:405`) names — and that declaration states the
      situation correctly (*"NOT dischargeable from `rlpItemDecode` alone"*), so the two
      disagreed with each other in the same file.

    ⇒ Restricting `bytes` so that this holds is exactly **route 1** (import a caller-side
    well-formedness fact), the option #11795 and #11898 both rejected — it was reached by
    accident, wearing route 2's label. Kept (not deleted) because
    `rlpItemDecodeBridgesFrom_of_walkNextStrict` consumes it and the implication is still
    true; what changes is that its hypothesis is now known to be a domain restriction
    rather than a scheduled proof. -/
def RlpWalkNextStrict (bytes : List (BitVec 8)) (base endPtr : Word) (floor : Nat) : Prop :=
  ∀ (off : Nat) (next len : Word),
    rlpItemDecode bytes off (base + BitVec.ofNat 64 off) endPtr next len →
    rlpItemDecodeStrict bytes off (base + BitVec.ofNat 64 off) endPtr next len
      (next - base).toNat floor

/-- Composing the two: the routine-side obligation yields the full per-item bridge, given
    the byte-string half that is already proven. This is the end-to-end shape #11795 asks
    for, with every remaining hypothesis about the ROUTINE rather than the model. -/
theorem rlpItemDecodeBridgesFrom_of_walkNextStrict {bytes : List (BitVec 8)}
    {base endPtr : Word} {floor : Nat}
    (hbytes : ∀ (off : Nat) (next len : Word) (b : BitVec 8),
      bytes[off]? = some b →
      BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true →
      rlpItemDecode bytes off (base + BitVec.ofNat 64 off) endPtr next len →
      ∃ item : RLPItem,
        decodeAux floor (bytes.drop off) = some (item, bytes.drop (next - base).toNat))
    (hstrict : RlpWalkNextStrict bytes base endPtr floor) :
    RlpItemDecodeBridgesFrom bytes base endPtr floor :=
  rlpItemDecodeBridgesFrom_of_parts hbytes (rlpListInteriorsDecode_of_strict hstrict)

/-! ## ⛔ Negative control: `RlpWalkNextStrict` is FALSE, not merely unproven

    A predicate that is quietly false is worse than an open goal: it reads as scheduled
    work, it makes every theorem consuming it vacuous on the domain that matters, and the
    next reader spends their time trying to prove it. So the refutation is checked by the
    kernel here rather than asserted in prose.

    The witness is the one `ItemDecodeForward.lean:10-14` already records as the reason
    the guest→model direction is false for the list disjuncts, reused rather than
    reinvented. -/

/-- `[0xc3, 0xc2, 0x81, 0x00]` — an outer 3-byte list containing a 2-byte list whose sole
    element is the **non-canonical** `81 00` (a one-byte string with content `< 0x80`,
    which RLP requires to use the single-byte form).

    The outer span is 4 bytes and fits the window, so the machine relation's short-list
    arm accepts it. The model rejects it two levels down. -/
private def nestedNonCanonical : List (BitVec 8) := [0xc3, 0xc2, 0x81, 0x00]

/-- The model rejects it, at the budget `decode` would supply (`2 * bs.length = 8`). -/
private theorem decodeAux_nestedNonCanonical :
    decodeAux 8 nestedNonCanonical = none := by
  decide

/-- The machine relation accepts it: the short-list arm asks only for header range and a
    span fit, and `4 = endPtr - cursor` fits exactly. -/
private theorem rlpItemDecode_nestedNonCanonical :
    rlpItemDecode nestedNonCanonical 0
      ((0x1000 : Word) + BitVec.ofNat 64 0) (0x1004 : Word) (0x1004 : Word) (4 : Word) := by
  refine ⟨0xc3, by decide, ?_⟩
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by decide, by decide, by decide, by decide, by decide⟩)))

/-- ⭐ **`RlpWalkNextStrict` is false.** Its hypothesis is the machine relation, which the
    counterexample satisfies; its conclusion needs the model decode, which fails. No
    strengthening of `rlp_walk_next` can change this, because the routine never appears in
    the statement — which is the point of recording it.

    Consequence for #11795: `rlpItemDecodeBridgesFrom_of_walkNextStrict` is a true
    implication whose hypothesis is **unsatisfiable on any byte string containing a
    span-fitting list with a malformed interior** — i.e. on exactly the MPT inline-node
    domain that made `rlp_list_count_items` need the bridge in the first place. -/
theorem not_rlpWalkNextStrict_nestedNonCanonical :
    ¬ RlpWalkNextStrict nestedNonCanonical (0x1000 : Word) (0x1004 : Word) 8 := by
  intro h
  obtain ⟨-, hpay⟩ := h 0 (0x1004 : Word) (4 : Word) rlpItemDecode_nestedNonCanonical
  obtain ⟨inner, hdec⟩ := hpay 0xc3 (by decide) (by decide)
  rw [show (nestedNonCanonical.drop 0) = nestedNonCanonical from rfl,
    decodeAux_nestedNonCanonical] at hdec
  exact absurd hdec.symm (Option.some_ne_none _)

/-! ## The residual, stated so that the routine actually appears in it

    What #11795 needs is not a fact about `bytes` but a fact about **acceptance**: when
    `rlp_walk_next` returns status 0, the model decode succeeds. `rlpItemDecode` is only a
    NECESSARY condition of acceptance (it is what the existing per-form postconditions
    pin), never a sufficient one — that asymmetry is the whole defect above.

    So the obligation is parameterised by the routine's accept predicate, left abstract
    here for a reason recorded below. -/

/-- The corrected residual: `accept off next len` — read as *"`rlp_walk_next` run at
    `base + off` returned status 0 with outputs `next`/`len`"* — implies the strict
    relation. Unlike `RlpWalkNextStrict` this is genuinely a routine obligation, because
    the antecedent is about a machine run rather than about `bytes`. -/
def RlpWalkNextAccepts (accept : Nat → Word → Word → Prop)
    (bytes : List (BitVec 8)) (base endPtr : Word) (floor : Nat) : Prop :=
  ∀ (off : Nat) (next len : Word),
    accept off next len →
    rlpItemDecodeStrict bytes off (base + BitVec.ofNat 64 off) endPtr next len
      (next - base).toNat floor

/-- The per-item bridge, restricted to offsets the routine actually accepted. This is the
    honest replacement for `rlpItemDecodeBridgesFrom_of_walkNextStrict`: same conclusion
    shape, but the quantifier ranges over accepted items instead of over everything the
    weak relation admits. -/
def RlpItemDecodeBridgesOn (accept : Nat → Word → Word → Prop)
    (bytes : List (BitVec 8)) (base : Word) (floor : Nat) : Prop :=
  ∀ (off : Nat) (next len : Word),
    accept off next len →
    ∃ item : RLPItem,
      decodeAux floor (bytes.drop off) = some (item, bytes.drop (next - base).toNat)

/-- ⭐ Given the corrected residual, the accept-indexed bridge follows for **both** prefix
    classes — lists from the strict conjunct, byte strings from the already-proven half —
    with no domain restriction on `bytes` anywhere.

    That it goes through cleanly is the evidence that the defect was in *where the
    quantifier sat*, not in the surrounding development: nothing else in this file had to
    change. -/
theorem rlpItemDecodeBridgesOn_of_accepts {accept : Nat → Word → Word → Prop}
    {bytes : List (BitVec 8)} {base endPtr : Word} {floor : Nat}
    (hbytes : ∀ (off : Nat) (next len : Word) (b : BitVec 8),
      bytes[off]? = some b →
      BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true →
      rlpItemDecode bytes off (base + BitVec.ofNat 64 off) endPtr next len →
      ∃ item : RLPItem,
        decodeAux floor (bytes.drop off) = some (item, bytes.drop (next - base).toNat))
    (haccept : RlpWalkNextAccepts accept bytes base endPtr floor) :
    RlpItemDecodeBridgesOn accept bytes base floor := by
  intro off next len hacc
  obtain ⟨hweak, hlist⟩ := haccept off next len hacc
  have hcopy := hweak
  obtain ⟨b, hget, -⟩ := hcopy
  by_cases hlt : BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true
  · exact hbytes off next len b hget hlt hweak
  · obtain ⟨inner, hdec⟩ := hlist b hget hlt
    exact ⟨.list inner, hdec⟩

/-! ## ⛔ Why `accept` is abstract, and what unblocks #11795

    `accept` is left as a parameter because **there is nothing to instantiate it with.**
    The interior validation that #11776 added lives in `rlpWalkNextFunction`
    (`RlpWalk.lean:155`), hand-written RISC-V emitted as a raw `String`. Measured against
    the guest image, the split is exact:

    | symbol | size | Lean representation |
    |---|---|---|
    | `rlp_walk_next` (entry) | 52 B | none |
    | `rlp_walk_next_nested` | 4 B | none |
    | `rlp_walk_next_shared` (the recursive validator) | 208 B | none |
    | `rlp_validate_payload` (the descent added by #11776) | 92 B | none |
    | `rlp_walk_next_core` (one item) | 412 B | `rlp_walk_next_prog`, 103 instrs |

    (sizes from `docs/4ch8f-guest-image-coverage.md:114-118`; the core's 103 × 4 = 412 B
    is what `rlpWalkNextCoreFunction_eq_verified_prog` (`RlpWalk.lean:264`) pins, and that
    theorem's own docstring calls the wrapper *"intentionally codegen-specific"*).

    So **356 of 768 bytes** have no model, and the 412 that do have one validate a single
    item — the half that was never in question.

    ⚠️ An earlier revision of this table listed four symbols and 264 bytes: it omitted
    `rlp_validate_payload` (`:117`), which sits inside the very line range the citation
    names. The omission mattered more than the arithmetic — that symbol is the descent
    #11776 *added*, i.e. the single most load-bearing unmodelled piece, and leaving it out
    made the gap look like plumbing around a validator rather than the validator itself.
    Corrected here rather than only on the issue, since a merged docstring is what a later
    reader cites.

    ⇒ The exact behaviour #11795 needs — recursive payload validation, exact cursor-to-end
    exhaustion, status 7 on nested-malformed interiors — is the behaviour that is NOT in
    the model. So the blocker is a **representation gap, not a proof effort**: the wrapper
    must become a `Program` before any triple about interior validation is statable, let
    alone provable. Sizing the bridge as "the walker's triple" understated it by the cost
    of an SAsm transcription.

    Until then `rlp_list_count_items` stays `.machineOnly`, and correctly so. -/

end EvmAsm.Codegen.RlpListCountItemsBridge
