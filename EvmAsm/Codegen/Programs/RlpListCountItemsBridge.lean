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
