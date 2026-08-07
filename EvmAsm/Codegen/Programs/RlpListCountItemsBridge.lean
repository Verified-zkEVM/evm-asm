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

end EvmAsm.Codegen.RlpListCountItemsBridge
