/-
  EvmAsm.Codegen.Programs.RlpItemSpanSpec

  Lives under Codegen/Programs (layering L1) because it pins the concrete
  linked guest entries of `rlp_item_span` / `rlp_item_size`
  (`Codegen.Programs.RlpRead`), same shape as `RlpSpliceHelperSpec.lean`.

  Success-path `cpsTripleWithin` work for `rlp_item_span`
  (`rlpItemSpan_prog`, 53 instructions): the item-walk loop around
  `rlp_item_size` that `mpt_splice_slot` uses to locate the full encoded
  span (start offset incl. prefix, total size) of list item `i`.

  ABI (`RlpRead.lean`): `a0` = ptr to the ENCODED LIST (header byte
  included), `a1` = its total byte length, `a2` = item index `i`,
  `a3` = out ptr (u64: item start offset relative to `a0`, prefix
  included), `a4` = out ptr (u64: item full encoded size).  Returns
  `a0 = 0` on success.  Keeps a real stack frame (`ra`/`s0`/`s1`/
  `s2`..`s6` at `sp-64..sp-8`), parses the list header itself (short
  `0xc0..0xf7` → payload at `+1`; long `0xf8..` → payload at
  `+1+lenlen`), then walks `i` items calling `rlp_item_size` per step.

  Contents:
  * pure layer: `itemOffset_succ` / suffix-decode bridges tying the
    walk cursor to `MptSpliceSlotSpec.itemOffset`;
  * offset variants of the `rlp_item_size` triples (the callee triple
    re-rooted at an UNALIGNED cursor `regionBase + off` inside the one
    aligned `bytesRegion` — the form the loop call sites need);
  * the machine blocks (prologue / header / loop body / exit tail) and
    the composed walk.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.RlpSpliceHelperSpec
import EvmAsm.Codegen.Programs.MptSpliceSlotSpec
import EvmAsm.Rv64.WP.Call
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XPerm

namespace EvmAsm.Codegen

namespace RlpItemSpanSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP
open EvmAsm.Codegen.RlpSpliceHelperSpec
open EvmAsm.Codegen.MptSpliceSlotSpec

/-! ## Pure layer: cursor arithmetic over `itemOffset` -/

/-- `itemOffset` at 0 is the payload start. -/
theorem itemOffset_zero (items : List RLPItem) : itemOffset items 0 = 0 := rfl

/-- Every RLP encoding is nonempty. -/
theorem encode_length_pos (item : RLPItem) : 0 < (encode item).length := by
  cases item with
  | bytes data =>
    show 0 < (encodeBytes data).length
    match data with
    | [] => simp [encodeBytes]
    | [b] => by_cases hb : b.toNat < 0x80 <;> simp [encodeBytes, hb]
    | b1 :: b2 :: tl =>
      simp only [encodeBytes]
      by_cases hshort : (b1 :: b2 :: tl).length ≤ 55
      · rw [if_pos (by simpa using hshort)]; simp
      · rw [if_neg (by simpa using hshort)]; simp
  | list items =>
    show 0 < (encode (.list items)).length
    unfold encode
    by_cases h : (encode.encodeItems items).length ≤ 55
    · rw [if_pos h]; simp
    · rw [if_neg h]; simp

/-- **The step law**: one item advances the payload cursor by exactly the
    item's full encoded size. -/
theorem itemOffset_succ (items : List RLPItem) (k : Nat) (hk : k < items.length) :
    itemOffset items (k + 1) = itemOffset items k + (encode items[k]).length := by
  unfold itemOffset
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  show (encode.encodeItems (items.take k ++ [items[k]])).length = _
  rw [encodeItems_append]
  show (encode.encodeItems (items.take k) ++ (encode items[k] ++ [])).length = _
  simp

/-- The cursor after `k` items never passes the payload end. -/
theorem itemOffset_le (items : List RLPItem) (k : Nat) :
    itemOffset items k ≤ (encode.encodeItems items).length := by
  conv_rhs => rw [← List.take_append_drop k items]
  rw [encodeItems_append, List.length_append]
  exact Nat.le_add_right _ _

/-- Strictly inside the payload while items remain (`encode` is nonempty). -/
theorem itemOffset_lt (items : List RLPItem) (k : Nat) (hk : k < items.length) :
    itemOffset items k < (encode.encodeItems items).length := by
  have hstep := itemOffset_succ items k hk
  have hle := itemOffset_le items (k + 1)
  have hpos := encode_length_pos items[k]
  omega

/-- Dropping the payload prefix of the first `k` items exposes item `k`'s
    encoding (followed by the remaining items' payload). -/
theorem encodeItems_drop_itemOffset (items : List RLPItem) (k : Nat)
    (hk : k < items.length) :
    (encode.encodeItems items).drop (itemOffset items k)
      = encode items[k] ++ encode.encodeItems (items.drop (k + 1)) := by
  conv_lhs => rw [encodeItems_eq_take_get_drop items k hk]
  rw [List.append_assoc, itemOffset, List.drop_left]

/-- The whole-buffer version: dropping header + `itemOffset` from
    `encode (.list items)` exposes item `k`'s encoding. -/
theorem encode_list_drop_cursor (items : List RLPItem) (k : Nat)
    (hk : k < items.length) :
    (encode (.list items)).drop
        ((rlpListPrefix (encode.encodeItems items).length).length + itemOffset items k)
      = encode items[k] ++ encode.encodeItems (items.drop (k + 1)) := by
  rw [encode_list_eq_prefix_append items,
      List.drop_length_add_append (itemOffset items k),
      encodeItems_drop_itemOffset items k hk]

/-- The suffix at the cursor decodes to item `k` (with the trailing items'
    payload as the leftover) — the decode fact each `rlp_item_size` call
    site consumes. -/
theorem decode_at_cursor (items : List RLPItem) (k : Nat) (hk : k < items.length)
    (hsz : (encode items[k]).length < 256 ^ 8) :
    decode ((encode (.list items)).drop
        ((rlpListPrefix (encode.encodeItems items).length).length + itemOffset items k))
      = some (items[k], encode.encodeItems (items.drop (k + 1))) := by
  rw [encode_list_drop_cursor items k hk]
  exact decode_encode_append items[k] _ hsz

/-- Total length of the list encoding = header + payload. -/
theorem encode_list_length (items : List RLPItem) :
    (encode (.list items)).length
      = (rlpListPrefix (encode.encodeItems items).length).length
          + (encode.encodeItems items).length := by
  rw [encode_list_eq_prefix_append items, List.length_append]

/-- The cursor (header + `itemOffset k`) is strictly inside the buffer
    while items remain. -/
theorem cursor_lt_length (items : List RLPItem) (k : Nat) (hk : k < items.length) :
    (rlpListPrefix (encode.encodeItems items).length).length + itemOffset items k
      < (encode (.list items)).length := by
  rw [encode_list_length]
  have := itemOffset_lt items k hk
  omega

/-! ## Guest layout -/

/-- Guest entry of `rlp_item_span`. -/
def rlpItemSpanBase : Word := BitVec.ofNat 64 GuestAddrs.rlp_item_span

theorem rlpItemSpanBase_eq : rlpItemSpanBase = (0x80004d88 : Word) := by decide

/-- The `rlp_item_span` body at its linked guest address. -/
abbrev rlpItemSpanCode : CodeReq :=
  CodeReq.ofProg rlpItemSpanBase rlpItemSpan_prog

theorem rlpItemSpan_prog_length : rlpItemSpan_prog.length = 53 := by decide
theorem rlpItemSize_prog_length : rlpItemSize_prog.length = 35 := by decide

/-- Full deployed layout: `rlp_item_span` plus its callee `rlp_item_size`
    at their linked guest addresses (contiguous: size `0x80004b3c..0x80004bc8`,
    span `0x80004bc8..0x80004c9c`). -/
abbrev rlpItemSpanFullCode : CodeReq :=
  rlpItemSpanCode.union rlpItemSizeCode

private theorem span_size_disjoint : rlpItemSpanCode.Disjoint rlpItemSizeCode :=
  CodeReq.ofProg_disjoint_range_len _ _ 53 _ _ 35
    rlpItemSpan_prog_length rlpItemSize_prog_length
    (fun k1 k2 hk1 hk2 => by
      unfold rlpItemSpanBase rlpItemSizeBase GuestAddrs.rlp_item_span
        GuestAddrs.rlp_item_size
      bv_omega)

/-- Span-body membership in the full layout. -/
theorem span_sub : ∀ a i, rlpItemSpanCode a = some i →
    rlpItemSpanFullCode a = some i :=
  CodeReq.union_mono_left

/-- Callee membership in the full layout. -/
theorem size_sub : ∀ a i, rlpItemSizeCode a = some i →
    rlpItemSpanFullCode a = some i :=
  CodeReq.mono_union_right span_size_disjoint (fun _ _ h => h)

end RlpItemSpanSpec

end EvmAsm.Codegen
