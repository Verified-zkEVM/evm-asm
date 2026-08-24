/-
  EvmAsm.Codegen.Programs.RlpItemSpanMachine

  Geometry, saved-register packaging and the PURE domain layer shared by
  every `rlp_item_span` arm (#11577; outer-header generalisation #10780).

  Domain gate (`.conditional`):
  * `bs = encode (.list items)` — a canonical list encoding.  The outer
    header may be EITHER form: the walk cursor is `listCursor`, whose
    header length is `hdrLen` (`1` short, `1 + lenlen` long), so the short
    (`ADDI s5, s0, 1`) and long (`SUB`/`ADDI`/`ADD`) arms share every
    cursor lemma below.  `hdrLen_short` / `hdrLen_long` are the only
    form-specific facts, and `long_list_head_toNat` /
    `long_head_sub_addi` are what the long machine block consumes;
  * `i < items.length`;
  * every item `0..i` has `SpanForm` head (the `rlp_item_size` callee domain);
  * `listBase % 8 = 0`, out ptrs 8-aligned, byte-validity, no word overflow.

  Non-vacuity lives here too: `rlp_item_span_precondition_reachable`
  (short) and `rlp_item_span_long_precondition_reachable` (long) exhibit
  concrete satisfying inputs, and `long_gate_negative_control` /
  `long_walk_negative_control` exhibit inputs where the long bundle's two
  halves are respectively FALSE — so neither conjunct is a tautology.

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

/-- Payload byte-length of the list. -/
def payloadLen (items : List RLPItem) : Nat :=
  (encode.encodeItems items).length

/-- Byte length of the OUTER list header: `1` for the short form
    (`payloadLen ≤ 55`), `1 + lenlen` for the long form.  Mirrors
    `ethereum_rlp.rlp.encode_sequence` (`0xC0 + len` vs
    `0xF7 + |BE len|`, execution-specs `e5a8caf1b`). -/
def hdrLen (items : List RLPItem) : Nat :=
  (rlpListPrefix (payloadLen items)).length

/-- Cursor (byte offset from listBase) of item `k`, outer header included.
    Header-form agnostic: the header length comes from `hdrLen`, so the
    same cursor serves the short (`0xC0+len`) and long (`0xF7+lenlen`)
    arms.  Matches the spec decoder's `joined_encodings_start_idx`
    (`rlp.py:428-434`). -/
def listCursor (items : List RLPItem) (k : Nat) : Nat :=
  hdrLen items + itemOffset items k

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

/-! ### Header-form-agnostic cursor arithmetic

`listCursor` reads its header length off `hdrLen`, so every lemma below is
shared by the short and long outer-header arms.  The two arms differ only
in `hdrLen_short` / `hdrLen_long`. -/

theorem listCursor_zero (items : List RLPItem) :
    listCursor items 0 = hdrLen items := by
  simp [listCursor, itemOffset, encode.encodeItems]

/-- Short outer header (`0xC0 + len`): one byte. -/
theorem hdrLen_short (items : List RLPItem) (h : payloadLen items ≤ 55) :
    hdrLen items = 1 := by
  unfold hdrLen
  exact rlpListPrefix_short_length _ h

/-- Long outer header (`0xF7 + lenlen`): `1 + lenlen` bytes. -/
theorem hdrLen_long (items : List RLPItem) (h : 56 ≤ payloadLen items) :
    hdrLen items = 1 + (Nat.toBytesBE (payloadLen items)).length := by
  unfold hdrLen
  rw [rlpListPrefix, if_neg (by omega : ¬ payloadLen items ≤ 55)]
  simp only [List.length_cons]
  omega

theorem listCursor_zero_short (items : List RLPItem) (h : payloadLen items ≤ 55) :
    listCursor items 0 = 1 := by
  rw [listCursor_zero, hdrLen_short items h]

theorem listCursor_zero_long (items : List RLPItem) (h : 56 ≤ payloadLen items) :
    listCursor items 0 = 1 + (Nat.toBytesBE (payloadLen items)).length := by
  rw [listCursor_zero, hdrLen_long items h]

theorem listCursor_succ (items : List RLPItem) (k : Nat)
    (hk : k < items.length) :
    listCursor items (k + 1)
      = listCursor items k + (encode items[k]).length := by
  simp only [listCursor, itemOffset_succ items k hk]
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

/-- Header + payload = buffer. -/
theorem encode_list_length_eq (items : List RLPItem) :
    (encode (.list items)).length = hdrLen items + payloadLen items := by
  unfold hdrLen payloadLen
  exact encode_list_length items

theorem payloadLen_le_encode (items : List RLPItem) :
    payloadLen items ≤ (encode (.list items)).length := by
  rw [encode_list_length_eq]; omega

/-- `|items| ≤ |encode (.list items)|` — the bound that replaces the
    short-list `≤ 55`, so the walk loop needs no payload-size gate. -/
theorem items_length_le_encode (items : List RLPItem) :
    items.length ≤ (encode (.list items)).length :=
  Nat.le_trans (items_length_le_payload items) (payloadLen_le_encode items)

/-- Item `k`'s encoding fits in the payload, hence in the buffer. -/
theorem encode_item_length_le_payload (items : List RLPItem) (k : Nat)
    (hk : k < items.length) :
    (encode items[k]).length ≤ payloadLen items := by
  have hstep := itemOffset_succ items k hk
  have hle := itemOffset_le items (k + 1)
  -- itemOffset (k+1) = itemOffset k + len ≤ payloadLen
  have hpos := encode_length_pos items[k]
  unfold payloadLen at *
  omega

theorem encode_item_length_le_encode (items : List RLPItem) (k : Nat)
    (hk : k < items.length) :
    (encode items[k]).length ≤ (encode (.list items)).length :=
  Nat.le_trans (encode_item_length_le_payload items k hk) (payloadLen_le_encode items)

/-- `256 ^ 8 = 2 ^ 64`, the form `decode_at_cursor`'s size gate wants. -/
private theorem pow256_eight : (256 : Nat) ^ 8 = 2 ^ 64 := by norm_num

/-- The callee's size gate, discharged from the buffer bound alone (no
    payload-length gate): item `k` is a slice of a buffer below `2 ^ 64`. -/
theorem encode_item_length_lt_bound (items : List RLPItem) (k : Nat)
    (hk : k < items.length)
    (hL : (encode (.list items)).length < 2 ^ 64) :
    (encode items[k]).length < 256 ^ 8 := by
  have := encode_item_length_le_encode items k hk
  rw [pow256_eight]
  omega

theorem listCursor_lt (items : List RLPItem) (k : Nat)
    (hk : k < items.length) :
    listCursor items k < (encode (.list items)).length := by
  unfold listCursor hdrLen payloadLen
  exact cursor_lt_length items k hk

theorem decode_at_listCursor (items : List RLPItem) (k : Nat)
    (hk : k < items.length) (hsz : (encode items[k]).length < 256 ^ 8) :
    decode ((encode (.list items)).drop (listCursor items k))
      = some (items[k], encode.encodeItems (items.drop (k + 1))) := by
  unfold listCursor hdrLen payloadLen
  exact decode_at_cursor items k hk hsz

/-- WalkedSpanForm head equals the byte at the walk cursor (via decode right-inverse). -/
theorem span_form_at_listCursor (items : List RLPItem) (k : Nat)
    (hk : k < items.length) (hsz : (encode (items[k]'hk)).length < 256 ^ 8)
    (hform : SpanForm ((encode (items[k]'hk)).getD 0 0)) :
    SpanForm (((encode (.list items)).drop (listCursor items k)).getD 0 0) := by
  have hdec := decode_at_listCursor items k hk hsz
  have henc := decode_eq_some_imp_encode _ _ _ hdec
  have hpos := encode_length_pos (items[k]'hk)
  have hhead :
      ((encode (.list items)).drop (listCursor items k)).getD 0 0
        = (encode (items[k]'hk)).getD 0 0 := by
    rw [henc]
    cases he : encode (items[k]'hk) with
    | nil =>
      have : (encode (items[k]'hk)).length = 0 := by simp [he]
      omega
    | cons b rest => simp
  rwa [hhead]

/-! ### Long outer header (`0xF7 + lenlen`)

Spec side: `ethereum_rlp.rlp.encode_sequence` emits
`Bytes([0xF7 + len(len_be)]) + len_be + payload` once the payload reaches
`0x38` bytes, and `decode_to_sequence` reads the payload back from
`joined_encodings_start_idx = 1 + encoded_sequence[0] - 0xF7`
(execution-specs `e5a8caf1b`, `ethereum_rlp/rlp.py:112-127` and
`:428-434`).  `hdrLen_long` is that index, and the three lemmas below pin
the head byte the guest dispatches on. -/

/-- The long-form head byte is `0xF7 + lenlen`. -/
theorem long_list_head (items : List RLPItem) (h : 56 ≤ payloadLen items) :
    (encode (.list items)).getD 0 0
      = BitVec.ofNat 8 (0xF7 + (Nat.toBytesBE (payloadLen items)).length) := by
  have hpl : payloadLen items = (encode.encodeItems items).length := rfl
  have hnle : ¬ (encode.encodeItems items).length ≤ 55 := by omega
  rw [encode_list_eq_prefix_append items, rlpListPrefix, if_neg hnle]
  simp only [List.cons_append, List.getD_cons_zero]
  rfl

/-- A long list's length field is nonempty (`payloadLen ≥ 56 > 0`). -/
theorem long_lenlen_pos (items : List RLPItem) (h : 56 ≤ payloadLen items) :
    0 < (Nat.toBytesBE (payloadLen items)).length := by
  obtain ⟨b, tl, hb, _⟩ := Nat.toBytesBE_eq_cons_of_pos (payloadLen items) (by omega)
  rw [hb]; simp

/-- A length field that fits the 64-bit envelope is at most 8 bytes, so the
    head byte stays inside `0xF8..0xFF`. -/
theorem long_lenlen_le_8 (items : List RLPItem)
    (hL : (encode (.list items)).length < 2 ^ 64) :
    (Nat.toBytesBE (payloadLen items)).length ≤ 8 := by
  have hp := payloadLen_le_encode items
  refine Nat.toBytesBE_length_le _ 8 ?_
  rw [pow256_eight]
  omega

theorem long_list_head_toNat (items : List RLPItem) (h : 56 ≤ payloadLen items)
    (hL : (encode (.list items)).length < 2 ^ 64) :
    ((encode (.list items)).getD 0 0).toNat
      = 0xF7 + (Nat.toBytesBE (payloadLen items)).length := by
  have hle := long_lenlen_le_8 items hL
  have h256 : (2 : Nat) ^ 8 = 256 := by norm_num
  have hlt : 0xF7 + (Nat.toBytesBE (payloadLen items)).length < 2 ^ 8 := by omega
  rw [long_list_head items h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- Long form ⇒ the guest's `BLTU x5, 0xF8` falls through. -/
theorem long_list_head_lo (items : List RLPItem) (h : 56 ≤ payloadLen items)
    (hL : (encode (.list items)).length < 2 ^ 64) :
    0xf8 ≤ ((encode (.list items)).getD 0 0).toNat := by
  have hpos := long_lenlen_pos items h
  rw [long_list_head_toNat items h hL]
  omega

/-- The `SUB x7, x5, 0xF7; ADDI x7, x7, 1` pair computes `hdrLen` exactly. -/
theorem long_head_sub_addi (b : BitVec 8) (n : Nat)
    (hb : b.toNat = 0xF7 + n) :
    (b.zeroExtend 64) - (247 : Word) + (1 : Word) = BitVec.ofNat 64 (1 + n) := by
  bv_omega

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

/-! ### Long-header coverRef and negative controls -/

private theorem encode_empty_bytes :
    encode (.bytes ([] : List Byte)) = [(0x80 : Byte)] := by
  simp [encode, encodeBytes]

/-- A list of `n` empty strings has payload `n` copies of `0x80`.  Gives a
    family of lists whose payload length is exactly `n`, so `n = 56` sits on
    the short/long outer-header boundary. -/
theorem encodeItems_replicate_empty (n : Nat) :
    encode.encodeItems (List.replicate n (.bytes ([] : List Byte)))
      = List.replicate n (0x80 : Byte) := by
  induction n with
  | zero => simp [encode.encodeItems]
  | succ m ih =>
    simp [List.replicate_succ, encode.encodeItems, encode_empty_bytes, ih]

/-- **Long-header coverRef.**  `items = 56 × .bytes []`: the payload is 56
    bytes, one past the short-form limit, so the outer header is the LONG
    form `[0xF8, 0x38]`; every walked item is `SpanForm` (`0x80 < 0xB8`);
    and the walk cursor of item 3 is `2 + 3 = 5`.  Exhibits the SMALLEST
    payload the long arm can see, so the arm is not reachable only in the
    large. -/
theorem rlp_item_span_long_precondition_reachable :
    let items : List RLPItem := List.replicate 56 (.bytes [])
    let i : Nat := 3
    56 ≤ payloadLen items
      ∧ i < items.length
      ∧ WalkedSpanForm items i
      ∧ hdrLen items = 2
      ∧ listCursor items i = 5
      ∧ encode (.list items)
          = (0xF8 : Byte) :: (0x38 : Byte) :: List.replicate 56 (0x80 : Byte) := by
  have hpl : payloadLen (List.replicate 56 (.bytes ([] : List Byte))) = 56 := by
    unfold payloadLen
    rw [encodeItems_replicate_empty]
    simp
  have hhdr : hdrLen (List.replicate 56 (.bytes ([] : List Byte))) = 2 := by
    unfold hdrLen
    rw [hpl, rlpListPrefix_long1 56 (by decide) (by decide)]
    rfl
  refine ⟨by omega, by simp, ?walk, hhdr, ?cur, ?enc⟩
  · intro k _hk1 hk2
    simp only [List.getElem_replicate]
    rw [encode_empty_bytes]
    exact Or.inl (by decide : ((0x80 : Byte).toNat < 0xb8))
  · unfold listCursor itemOffset
    rw [hhdr,
      show (List.replicate 56 (RLPItem.bytes [])).take 3
          = List.replicate 3 (RLPItem.bytes []) from by simp,
      encodeItems_replicate_empty]
    simp
  · rw [encode_list_eq_prefix_append (List.replicate 56 (.bytes [])),
      encodeItems_replicate_empty,
      show (List.replicate 56 (0x80 : Byte)).length = 56 from by simp,
      rlpListPrefix_long1 56 (by decide) (by decide)]
    rfl

/-- **Negative control 1** for the long arm: the gate is a real restriction,
    not a tautology — the SHORT coverRef's own witness refutes it. -/
theorem long_gate_negative_control :
    ¬ (56 ≤ payloadLen [RLPItem.bytes []]) := by
  have hitems : encode.encodeItems [.bytes ([] : List Byte)] = [(0x80 : Byte)] := by
    simp [encode.encodeItems, encode_empty_bytes]
  simp [payloadLen, hitems]

/-- **Negative control 2**: the long outer header does NOT imply
    `WalkedSpanForm`.  A single 56-byte string has payload `57 + lenlen ≥ 58`
    — a long outer header — yet its own head byte is `0xB7 + lenlen ∈
    0xB8..0xBF`, exactly the long-STRING band `SpanForm` excludes.  So the
    two halves of the bundle are independent and neither is vacuous. -/
theorem long_walk_negative_control :
    let items : List RLPItem := [.bytes (List.replicate 56 (0 : Byte))]
    56 ≤ payloadLen items ∧ ¬ WalkedSpanForm items 0 := by
  set data : List Byte := List.replicate 56 (0 : Byte) with hdata
  have hdlen : data.length = 56 := by simp [hdata]
  have hll_pos : 0 < (Nat.toBytesBE data.length).length := by
    obtain ⟨b, tl, hb, _⟩ := Nat.toBytesBE_eq_cons_of_pos data.length (by omega)
    rw [hb]; simp
  have hll_le : (Nat.toBytesBE data.length).length ≤ 8 :=
    Nat.toBytesBE_length_le _ 8 (by rw [hdlen]; norm_num)
  have henc : encode (.bytes data)
      = [BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length)]
          ++ Nat.toBytesBE data.length ++ data := by
    show encodeBytes data = _
    exact encodeBytes_long_of_length data (by omega)
  have hhead : (encode (.bytes data)).getD 0 0
      = BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length) := by
    rw [henc]; simp
  have hhead_toNat : ((encode (.bytes data)).getD 0 0).toNat
      = 0xB7 + (Nat.toBytesBE data.length).length := by
    have h256 : (2 : Nat) ^ 8 = 256 := by norm_num
    rw [hhead, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlen : (encode (.bytes data)).length
      = 1 + (Nat.toBytesBE data.length).length + 56 := by
    rw [henc]
    simp only [List.length_append, List.length_cons, List.length_nil, hdlen]
  have hitems : encode.encodeItems [RLPItem.bytes data] = encode (.bytes data) := by
    simp [encode.encodeItems]
  refine ⟨?_, ?_⟩
  · unfold payloadLen
    rw [hitems, hlen]
    omega
  · intro hwalk
    have h0 := hwalk 0 (Nat.le_refl _) (by simp)
    simp only [List.getElem_cons_zero, SpanForm, hhead_toNat] at h0
    rcases h0 with h | ⟨h, _⟩ <;> omega

end RlpItemSpanSpec
end EvmAsm.Codegen
