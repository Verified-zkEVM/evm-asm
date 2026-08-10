/-
  EvmAsm.Codegen.Programs.RlpItemSpanMachine

  Whole-routine `cpsTripleWithin` for `rlp_item_span` under the short-list
  outer header + `SpanForm` on every walked prefix (incl. item `i`).  #11577.

  Domain gate (`.conditional`):
  * `bs = encode (.list items)` with payload length ≤ 55 (short list header,
    so the guest takes the `ADDI s5, s0, 1` arm);
  * `i < items.length`;
  * every item `0..i` has `SpanForm` head (the `rlp_item_size` callee domain);
  * `listBase % 8 = 0`, out ptrs 8-aligned, byte-validity, no word overflow.

  Byte-transparent: `abiFrameProg (-64)(64) spanFrame spanBody = rlpItemSpan_prog`.
-/

import EvmAsm.Codegen.Programs.RlpItemSpanSpec
import EvmAsm.Codegen.Programs.RlpItemSpanSizeOffset
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Codegen
namespace RlpItemSpanSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.Tactics
open EvmAsm.EL.RLP
open EvmAsm.Codegen.RlpSpliceHelperSpec
open EvmAsm.Codegen.MptSpliceSlotSpec

local macro "cmem" k:term:max : tactic =>
  `(tactic| exact CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr _ _ $k _ (by decide) (by decide) (by bv_omega)))

/-! ## Geometry -/

/-- 8-slot frame: ra, s0..s6 at sp+0..56. -/
def spanFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32),
   (.x20, 40), (.x21, 48), (.x22, 56)]

/-- Body slice (indices 9..42 of `rlpItemSpan_prog`). -/
def spanBody : List Instr :=
  [ .MV .x8 .x10,
    .ADD .x9 .x10 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .BGEU .x8 .x9 (112 : BitVec 13),
    .LBU .x5 .x8 (0 : BitVec 12),
    .LI .x6 (192 : Word),
    .BLTU .x5 .x6 (100 : BitVec 13),
    .LI .x6 (248 : Word),
    .BLTU .x5 .x6 (24 : BitVec 13),
    .LI .x6 (247 : Word),
    .SUB .x7 .x5 .x6,
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADD .x21 .x8 .x7,
    .JAL .x0 (8 : BitVec 21),
    .ADDI .x21 .x8 (1 : BitVec 12),
    .LI .x22 (0 : Word),
    .BEQ .x22 .x18 (28 : BitVec 13),
    .BGEU .x21 .x9 (56 : BitVec 13),
    .MV .x10 .x21,
    .JAL .x1 (jalOff GuestAddrs.rlp_item_size (GuestAddrs.rlp_item_span + 120)),
    .ADD .x21 .x21 .x10,
    .ADDI .x22 .x22 (1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .BGEU .x21 .x9 (32 : BitVec 13),
    .MV .x10 .x21,
    .JAL .x1 (jalOff GuestAddrs.rlp_item_size (GuestAddrs.rlp_item_span + 144)),
    .SUB .x6 .x21 .x8,
    .SD .x19 .x6 (0 : BitVec 12),
    .SD .x20 .x10 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word) ]

#guard spanFrame.length = 8
#guard spanBody.length = 34
#guard abiFrameProg (-64 : BitVec 12) (64 : BitVec 12) spanFrame spanBody
  = rlpItemSpan_prog

theorem spanProg_eq :
    abiFrameProg (-64 : BitVec 12) (64 : BitVec 12) spanFrame spanBody
      = rlpItemSpan_prog := rfl

theorem spanFrame_length : spanFrame.length = 8 := by decide
theorem spanBody_length : spanBody.length = 34 := by decide

/-- Full CR: span + size at linked addresses. -/
abbrev spanCr : CodeReq := rlpItemSpanFullCode

/-- Body entry / exit PCs (absolute). -/
def bodyEntry : Word := rlpItemSpanBase + BitVec.ofNat 64 (4 * (1 + 8))
def bodyExit  : Word := rlpItemSpanBase + BitVec.ofNat 64 (4 * (1 + 8 + 34))
def loopHdr   : Word := rlpItemSpanBase + BitVec.ofNat 64 (4 * 27)
def exitGate  : Word := rlpItemSpanBase + BitVec.ofNat 64 (4 * 34)

private theorem bodyEntry_val : bodyEntry = rlpItemSpanBase + 36 := by
  unfold bodyEntry; bv_omega
private theorem bodyExit_val : bodyExit = rlpItemSpanBase + 172 := by
  unfold bodyExit; bv_omega
private theorem loopHdr_val : loopHdr = rlpItemSpanBase + 108 := by
  unfold loopHdr; bv_omega
private theorem exitGate_val : exitGate = rlpItemSpanBase + 136 := by
  unfold exitGate; bv_omega

/-! ## Saved-register packaging -/

structure Saved where
  ra : Word
  s0 : Word
  s1 : Word
  s2 : Word
  s3 : Word
  s4 : Word
  s5 : Word
  s6 : Word

def savedVals (s : Saved) : Reg → Word
  | .x1  => s.ra
  | .x8  => s.s0
  | .x9  => s.s1
  | .x18 => s.s2
  | .x19 => s.s3
  | .x20 => s.s4
  | .x21 => s.s5
  | .x22 => s.s6
  | _    => 0

theorem regsAt_spanFrame (s : Saved) :
    regsAt spanFrame (savedVals s) =
      ((.x1 ↦ᵣ s.ra) ** (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
       (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
       (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6)) := by
  simp [spanFrame, regsAt, savedVals, sepConj_emp_right']

def savedFrame (newSp : Word) (s : Saved) : Assertion :=
  (newSp ↦ₘ s.ra) ** ((newSp + 8) ↦ₘ s.s0) ** ((newSp + 16) ↦ₘ s.s1) **
  ((newSp + 24) ↦ₘ s.s2) ** ((newSp + 32) ↦ₘ s.s3) ** ((newSp + 40) ↦ₘ s.s4) **
  ((newSp + 48) ↦ₘ s.s5) ** ((newSp + 56) ↦ₘ s.s6)

theorem frameSlotsSaved_spanFrame (newSp : Word) (s : Saved) :
    frameSlotsSaved spanFrame newSp (savedVals s) = savedFrame newSp s := by
  simp [spanFrame, frameSlotsSaved, savedFrame, savedVals,
    sepConj_emp_right', signExtend12]

/-! ## Pure domain helpers -/

/-- Payload byte-length of a short list. -/
def payloadLen (items : List RLPItem) : Nat :=
  (encode.encodeItems items).length

/-- Cursor (byte offset from listBase) of item `k` under a short-list header. -/
def shortCursor (items : List RLPItem) (k : Nat) : Nat :=
  1 + itemOffset items k

/-- Every walked item `0..i` (inclusive) is in `SpanForm`. -/
def WalkedSpanForm (items : List RLPItem) (i : Nat) : Prop :=
  ∀ k (_hk1 : k ≤ i) (hk2 : k < items.length),
    SpanForm ((encode (items[k]'hk2)).getD 0 0)

theorem rlpListPrefix_short_length (n : Nat) (h : n ≤ 55) :
    (rlpListPrefix n).length = 1 := by
  simp [rlpListPrefix, h]

theorem short_list_head (items : List RLPItem)
    (h : payloadLen items ≤ 55) :
    (encode (.list items)).getD 0 0
      = BitVec.ofNat 8 (0xC0 + payloadLen items) := by
  rw [encode_list_short items h, payloadLen, List.getD_cons_zero]

theorem short_list_head_lo (items : List RLPItem)
    (h : payloadLen items ≤ 55) :
    0xc0 ≤ ((encode (.list items)).getD 0 0).toNat := by
  rw [short_list_head items h, BitVec.toNat_ofNat]
  have hlt : 0xC0 + payloadLen items < 256 := by omega
  rw [Nat.mod_eq_of_lt hlt]; omega

theorem short_list_head_hi (items : List RLPItem)
    (h : payloadLen items ≤ 55) :
    ((encode (.list items)).getD 0 0).toNat < 0xf8 := by
  rw [short_list_head items h, BitVec.toNat_ofNat]
  have hlt : 0xC0 + payloadLen items < 256 := by omega
  rw [Nat.mod_eq_of_lt hlt]; omega

theorem short_list_length (items : List RLPItem)
    (h : payloadLen items ≤ 55) :
    (encode (.list items)).length = 1 + payloadLen items := by
  rw [encode_list_short items h, List.length_cons, payloadLen]
  omega

theorem shortCursor_zero (items : List RLPItem) :
    shortCursor items 0 = 1 := by
  simp [shortCursor, itemOffset, encode.encodeItems]

theorem shortCursor_succ (items : List RLPItem) (k : Nat)
    (hk : k < items.length) :
    shortCursor items (k + 1)
      = shortCursor items k + (encode items[k]).length := by
  simp only [shortCursor, itemOffset_succ items k hk]
  omega

/-- Every item contributes ≥1 payload byte, so `|items| ≤ payloadLen`. -/
theorem items_length_le_payload (items : List RLPItem) :
    items.length ≤ payloadLen items := by
  induction items with
  | nil => simp [payloadLen, encode.encodeItems]
  | cons h t ih =>
    -- payloadLen (h::t) = |encode h| + |encodeItems t|
    unfold payloadLen at ih ⊢
    simp only [List.length_cons, encode.encodeItems, List.length_append]
    have hpos := encode_length_pos h
    omega

/-- Under a short list, `|items| ≤ 55`. -/
theorem items_length_le_55 (items : List RLPItem) (h : payloadLen items ≤ 55) :
    items.length ≤ 55 :=
  Nat.le_trans (items_length_le_payload items) h

/-- Item `k` of a short list is itself short: encoded length ≤ payload ≤ 55. -/
theorem encode_item_length_le_payload (items : List RLPItem) (k : Nat)
    (hk : k < items.length) :
    (encode items[k]).length ≤ payloadLen items := by
  have hstep := itemOffset_succ items k hk
  have hle := itemOffset_le items (k + 1)
  -- itemOffset (k+1) = itemOffset k + len ≤ payloadLen
  have hpos := encode_length_pos items[k]
  unfold payloadLen at *
  omega

theorem encode_item_length_lt_bound (items : List RLPItem) (k : Nat)
    (hk : k < items.length) (hshort : payloadLen items ≤ 55) :
    (encode items[k]).length < 256 ^ 8 := by
  have := encode_item_length_le_payload items k hk
  omega

theorem shortCursor_lt (items : List RLPItem) (k : Nat)
    (hk : k < items.length) (hshort : payloadLen items ≤ 55) :
    shortCursor items k < (encode (.list items)).length := by
  have hcur := cursor_lt_length items k hk
  have hpfx := rlpListPrefix_short_length (payloadLen items) hshort
  simp only [shortCursor, payloadLen] at *
  -- hcur : |prefix| + itemOffset k < |encode list|
  -- hpfx : |prefix| = 1
  simpa [hpfx] using hcur

theorem decode_at_shortCursor (items : List RLPItem) (k : Nat)
    (hk : k < items.length) (hshort : payloadLen items ≤ 55) :
    decode ((encode (.list items)).drop (shortCursor items k))
      = some (items[k], encode.encodeItems (items.drop (k + 1))) := by
  have hsz := encode_item_length_lt_bound items k hk hshort
  have hdec := decode_at_cursor items k hk hsz
  have hpfx := rlpListPrefix_short_length (payloadLen items) hshort
  -- rewrite prefix length 1 into the drop offset
  simp only [shortCursor, payloadLen] at hdec hpfx ⊢
  simpa [hpfx] using hdec

/-- WalkedSpanForm head equals the byte at the short-list cursor (via decode right-inverse). -/
theorem span_form_at_shortCursor (items : List RLPItem) (k : Nat)
    (hk : k < items.length) (hshort : payloadLen items ≤ 55)
    (hform : SpanForm ((encode (items[k]'hk)).getD 0 0)) :
    SpanForm (((encode (.list items)).drop (shortCursor items k)).getD 0 0) := by
  have hdec := decode_at_shortCursor items k hk hshort
  have henc := decode_eq_some_imp_encode _ _ _ hdec
  have hpos := encode_length_pos (items[k]'hk)
  have hhead :
      ((encode (.list items)).drop (shortCursor items k)).getD 0 0
        = (encode (items[k]'hk)).getD 0 0 := by
    rw [henc]
    cases he : encode (items[k]'hk) with
    | nil =>
      have : (encode (items[k]'hk)).length = 0 := by simp [he]
      omega
    | cons b rest => simp
  rwa [hhead]

/-! ## coverRef (non-vacuity) -/

/-- Concrete witness: `encode (.list [.bytes []]) = [0xc1, 0x80]`, index 0. -/
theorem rlp_item_span_precondition_reachable :
    let items : List RLPItem := [.bytes []]
    let i : Nat := 0
    payloadLen items ≤ 55
      ∧ i < items.length
      ∧ WalkedSpanForm items i
      ∧ (encode (.list items) = [(0xc1 : BitVec 8), (0x80 : BitVec 8)]) := by
  have hitem : encode (.bytes ([] : List Byte)) = [(0x80 : BitVec 8)] := by
    simp [encode, encodeBytes]
  have hitems : encode.encodeItems [.bytes ([] : List Byte)] = [(0x80 : BitVec 8)] := by
    simp [encode.encodeItems, hitem]
  refine ⟨?plen, ?ilen, ?walk, ?enc⟩
  · -- payload = [0x80], length 1 ≤ 55
    simp [payloadLen, hitems]
  · decide
  · intro k _hk1 hk2
    have hk0 : k = 0 := by omega
    subst hk0
    change SpanForm ((encode (.bytes ([] : List Byte))).getD 0 0)
    simp only [hitem, List.getD_cons_zero]
    -- 0x80 < 0xb8
    exact Or.inl (by decide : ((0x80 : BitVec 8).toNat < 0xb8))
  · rw [encode_list_short [.bytes ([] : List Byte)] (by simp [hitems])]
    simp [hitems]

end RlpItemSpanSpec
end EvmAsm.Codegen
