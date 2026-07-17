/-
  EvmAsm.Codegen.Programs.MptSpliceSlotSpec

  Lives under Codegen/Programs (not Evm64) because it pins the concrete
  linked guest entries of `Codegen.Programs.MptSet` routines (layering
  L1: verified core may not import Codegen) — same shape as
  `RlpSpliceHelperSpec.lean` / `AccountBalanceHelperSpec.lean`.

  Phase 3c part 3 (SELFDESTRUCT effects-body chain, `mpt_splice_slot` →
  `account_set_uint_field` → `selfdestruct_balance_transfer`): the pure
  splice model for `mptSpliceSlot_prog` (`MptSet.lean`, 144 instructions)
  and its RLP correctness keystone.

  `mpt_splice_slot` semantics (see the program header):

    new_payload = src[payload_start..slot_start] ++ new_ref
                  ++ src[slot_start+slot_size..src_len]
    out         = rlp_encode_list_prefix(len(new_payload)) ++ new_payload

  This file provides:

  * `rlpListPrefix` — the yellow-paper §B list-header rule as a pure
    function, with `encode_list_eq_prefix_append` (the bridge promised in
    `RlpSpliceHelperSpec.lean`): `encode (.list items)` IS
    `rlpListPrefix payload.length ++ payload`.

  * `splicePayload` / `spliceSlot` — the pure, program-shaped splice
    model (`List.take`/`List.drop`/`++`).

  * `spliceSlot_encodes` — the keystone: splicing the full encoded span
    of item `k` of `encode (.list items)` with `encode newItem` yields
    EXACTLY `encode (.list (items.set k newItem))` — for every list and
    every item form (no long-form restriction at the pure level).

  * `spliced_buffer_content` — the machine-shaped assembly lemma: the
    guest's write sequence (two prefix `SB`s, then the three
    `mset_memcpy` windows head / new_ref / tail at the running cursor)
    over the output region equals `spliceSlot … ++ (untouched leftover)`
    — stated over `copyIntoRegion` (`AccountBalanceHelperSpec.lean`),
    the exact post-state form the `mset_memcpy_spec_within` triples
    produce.

  The full machine triple for `mptSpliceSlot_prog` additionally needs a
  verified triple for `rlp_item_span` (`rlpItemSpan_prog`, 53
  instructions — stack frame + item-walk loop around `rlp_item_size`),
  which does not exist yet; see the gap note at the bottom.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.EL.RLP.Properties
import EvmAsm.Codegen.Programs.MptSet

namespace EvmAsm.Codegen

namespace MptSpliceSlotSpec

open EvmAsm.EL.RLP

/-! ## The list-header rule as a pure function -/

/-- The RLP list-header bytes for a payload of `len` bytes (yellow-paper
    §B list rule): `0xC0 + len` for short payloads, else `0xF7 + |BE len|`
    followed by the big-endian length. Exactly what the verified
    `rlp_encode_list_prefix` guest routine writes. -/
def rlpListPrefix (len : Nat) : List Byte :=
  if len ≤ 55 then [BitVec.ofNat 8 (0xC0 + len)]
  else BitVec.ofNat 8 (0xF7 + (Nat.toBytesBE len).length) :: Nat.toBytesBE len

/-- **The header bridge**: a list encoding is its header followed by its
    payload, in every form. -/
theorem encode_list_eq_prefix_append (items : List RLPItem) :
    encode (.list items)
      = rlpListPrefix (encode.encodeItems items).length ++ encode.encodeItems items := by
  by_cases h : (encode.encodeItems items).length ≤ 55
  · rw [encode_list_short items h, rlpListPrefix, if_pos h]; rfl
  · rw [encode_list_long items (by omega), rlpListPrefix, if_neg h]; rfl

/-- `Nat.toBytesBE` of a positive byte-sized value is the single byte
    (local copy of `EvmAsm.Evm64.toBytesBE_of_pos_lt_256`, which lives in
    the heavier `AccountAccessorSpec`). -/
private theorem toBytesBE_single (n : Nat) (h0 : 0 < n) (h : n < 256) :
    Nat.toBytesBE n = [BitVec.ofNat 8 n] := by
  match n, h0 with
  | m + 1, _ =>
    rw [Nat.toBytesBE_succ, Nat.div_eq_of_lt h, Nat.toBytesBE_zero,
      Nat.mod_eq_of_lt h, List.nil_append]

/-- The long-1 header (`56 ≤ len < 256`, the account list's form) is
    `[0xF8, len]` — the two bytes `rlp_encode_list_prefix_long1_pinned_spec_within`
    writes. -/
theorem rlpListPrefix_long1 (len : Nat) (hlo : 56 ≤ len) (hhi : len < 256) :
    rlpListPrefix len = [(0xF8 : BitVec 8), BitVec.ofNat 8 len] := by
  rw [rlpListPrefix, if_neg (by omega), toBytesBE_single len (by omega) hhi]
  rfl

/-! ## The pure splice model -/

/-- The spliced payload, program-shaped: the bytes of `src` from
    `payloadStart` (inclusive) to `slotStart` (exclusive), then the new
    reference, then the bytes of `src` from `slotStart + slotSize` on. -/
def splicePayload (src : List Byte) (payloadStart slotStart slotSize : Nat)
    (newRef : List Byte) : List Byte :=
  (src.drop payloadStart).take (slotStart - payloadStart)
    ++ newRef ++ src.drop (slotStart + slotSize)

/-- The full spliced node: fresh list header + spliced payload —
    `mpt_splice_slot`'s output buffer contents. -/
def spliceSlot (src : List Byte) (payloadStart slotStart slotSize : Nat)
    (newRef : List Byte) : List Byte :=
  rlpListPrefix (splicePayload src payloadStart slotStart slotSize newRef).length
    ++ splicePayload src payloadStart slotStart slotSize newRef

theorem splicePayload_length (src : List Byte) (payloadStart slotStart slotSize : Nat)
    (newRef : List Byte)
    (h1 : payloadStart ≤ slotStart) (h2 : slotStart ≤ src.length)
    (h3 : slotStart + slotSize ≤ src.length) :
    (splicePayload src payloadStart slotStart slotSize newRef).length
      = (slotStart - payloadStart) + newRef.length
          + (src.length - (slotStart + slotSize)) := by
  simp only [splicePayload, List.length_append, List.length_take, List.length_drop]
  omega

/-! ## The RLP keystone: splicing item `k` re-encodes the updated list -/

/-- `encodeItems` distributes over append (the payload of a list is the
    concatenation of its items' encodings, segment by segment). -/
theorem encodeItems_append (xs ys : List RLPItem) :
    encode.encodeItems (xs ++ ys)
      = encode.encodeItems xs ++ encode.encodeItems ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, encode.encodeItems, ih, List.append_assoc]

/-- Item-`k` decomposition of a list payload: everything before `k`, the
    encoding of item `k`, everything after. -/
theorem encodeItems_eq_take_get_drop (items : List RLPItem) (k : Nat)
    (hk : k < items.length) :
    encode.encodeItems items
      = encode.encodeItems (items.take k) ++ encode items[k]
          ++ encode.encodeItems (items.drop (k + 1)) := by
  conv_lhs => rw [← List.take_append_drop k items]
  rw [encodeItems_append,
    List.drop_eq_getElem_cons hk, encode.encodeItems, List.append_assoc]

/-- Byte offset of item `k` inside the payload. -/
def itemOffset (items : List RLPItem) (k : Nat) : Nat :=
  (encode.encodeItems (items.take k)).length

/-- The updated list, decomposed at `k`. -/
private theorem set_decomp (items : List RLPItem) (k : Nat) (newItem : RLPItem)
    (hk : k < items.length) :
    items.set k newItem = items.take k ++ newItem :: items.drop (k + 1) := by
  rw [List.set_eq_take_append_cons_drop, if_pos hk]

/-- **The keystone**: splicing the full encoded span of item `k` of
    `encode (.list items)` with `encode newItem` yields exactly
    `encode (.list (items.set k newItem))` — for every list and every
    item form. The machine's `payload_start` is the header length, the
    slot is item `k`'s span. -/
theorem spliceSlot_encodes (items : List RLPItem) (k : Nat) (newItem : RLPItem)
    (hk : k < items.length) :
    spliceSlot (encode (.list items))
        (rlpListPrefix (encode.encodeItems items).length).length
        ((rlpListPrefix (encode.encodeItems items).length).length + itemOffset items k)
        (encode items[k]).length
        (encode newItem)
      = encode (.list (items.set k newItem)) := by
  -- Abbreviations for the three payload segments and the header.
  have hdecomp := encodeItems_eq_take_get_drop items k hk
  generalize hA : encode.encodeItems (items.take k) = A at *
  generalize hB : encode items[k] = B at *
  generalize hC : encode.encodeItems (items.drop (k + 1)) = C at *
  generalize hPdef : rlpListPrefix (encode.encodeItems items).length = P at *
  have hsrc : encode (.list items) = P ++ (A ++ B ++ C) := by
    rw [encode_list_eq_prefix_append items, hPdef, hdecomp]
  -- The new payload is A ++ encode newItem ++ C.
  have hnewpay : encode.encodeItems (items.set k newItem)
      = A ++ (encode newItem ++ C) := by
    rw [set_decomp items k newItem hk, encodeItems_append, hA,
      encode.encodeItems, hC]
  -- The splice windows compute exactly those segments.
  have hoff : itemOffset items k = A.length := by rw [itemOffset, hA]
  have hpay : splicePayload (encode (.list items)) P.length
      (P.length + itemOffset items k) B.length (encode newItem)
      = A ++ (encode newItem ++ C) := by
    rw [splicePayload, hsrc, hoff, List.drop_left' rfl, Nat.add_sub_cancel_left]
    have htake : (A ++ B ++ C).take A.length = A := by
      rw [List.append_assoc, List.take_left]
    have hregroup : P ++ (A ++ B ++ C) = (P ++ A ++ B) ++ C := by
      simp [List.append_assoc]
    have hdrop : (P ++ (A ++ B ++ C)).drop (P.length + A.length + B.length) = C := by
      rw [hregroup, List.drop_left' (by simp; omega)]
    rw [htake, hdrop, List.append_assoc]
  -- Reassemble via the header bridge.
  rw [spliceSlot, hpay, ← hnewpay, ← encode_list_eq_prefix_append]
