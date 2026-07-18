/-
  Pure honesty substrate for ExtractAssumed packaging.

  Connects `extractSuccess` (EL decode model) toward walk-machine residuals
  (`hcre` / `hlen20` / `rlpItemDecode` at field offsets). Full machine bridge
  (hdrop / hok* / hnext* universal packaging) remains residual.
-/

import EvmAsm.Rv64.Basic
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.EL.RLP.Properties
import EvmAsm.Codegen.Programs.TxExtractToAddressModel
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Rv64.SAsm.LoopFuel

namespace EvmAsm.Codegen.TxExtractToAddressHonesty

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Rv64.SAsm (toNat_zeroExtend_byte)
open EvmAsm.EL.RLP
open EvmAsm.Codegen.TxExtractToAddressModel
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch)

/-- Empty short string `0x80` at `off` with fit ⇒ `rlpItemDecode` len=0
    (hcre pure half for creation). `hfit`: `0 < end-cursor` i.e. room for header. -/
theorem rlpItemDecode_empty_short
    (bytes : List (BitVec 8)) (off : Nat) (cursor endPtr : Word)
    (hoff : off < bytes.length)
    (hb : bytes[off]'hoff = (0x80 : BitVec 8))
    (hfit : BitVec.ult (0 : Word) (endPtr - cursor) = true) :
    rlpItemDecode bytes off cursor endPtr
      (cursor + signExtend12 (1 : BitVec 12)) (0 : Word) := by
  refine ⟨(0x80 : BitVec 8), ?_, Or.inr (Or.inl ?_)⟩
  · rw [List.getElem?_eq_getElem hoff, hb]
  · have hge : ¬ BitVec.ult ((0x80 : BitVec 8).zeroExtend 64) (0x80 : Word) = true := by
      decide
    have hlt : BitVec.ult ((0x80 : BitVec 8).zeroExtend 64) (0xb8 : Word) = true := by
      decide
    have hlen0 : (0x80 : BitVec 8).zeroExtend 64 - (0x80 : Word) = (0 : Word) := by
      decide
    refine ⟨hge, hlt, ?_, ?_, ?_, ?_⟩
    · intro h1
      rw [hlen0] at h1
      exact absurd h1 (by decide)
    · rwa [hlen0]
    · rw [hlen0]
      exact (BitVec.add_zero _).symm
    · exact hlen0

/-- Empty short string at `off` ⇒ walk_next OK assertion on matching regs. -/
theorem rlpWalkNextOk_empty_short
    (srcBase endPtr : Word) (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (hoff : srcOff < srcBytes.length)
    (hb : srcBytes[srcOff]'hoff = (0x80 : BitVec 8))
    (hfit : BitVec.ult (0 : Word)
      (endPtr - (srcBase + BitVec.ofNat 64 srcOff)) = true) :
    ∀ h,
      ((.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word))) h →
      rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr srcBytes srcOff h := by
  intro h hp
  refine ⟨(srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12),
    (0 : Word), ?_⟩
  have hdec := rlpItemDecode_empty_short srcBytes srcOff
    (srcBase + BitVec.ofNat 64 srcOff) endPtr hoff hb hfit
  have hleft :
      (((((Reg.x10 ↦ᵣ
            (srcBase + BitVec.ofNat 64 srcOff + signExtend12 (1 : BitVec 12))) **
          (Reg.x11 ↦ᵣ (0 : Word))) ** (Reg.x12 ↦ᵣ (0 : Word))) **
        ⌜rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr
          (srcBase + BitVec.ofNat 64 srcOff + signExtend12 (1 : BitVec 12))
          (0 : Word)⌝) h) :=
    (sepConj_pure_right h).2 ⟨by xperm_hyp hp, hdec⟩
  xperm_hyp hleft

/-- 20-byte short string prefix `0x94` (= 0x80+20) with fit ⇒ `rlpItemDecode` len=20.
    (hlen20 pure half when field is 20-byte address; canonicity vacuous since len≠1.) -/
theorem rlpItemDecode_addr20_short
    (bytes : List (BitVec 8)) (off : Nat) (cursor endPtr : Word)
    (hoff : off < bytes.length)
    (hb : bytes[off]'hoff = (0x94 : BitVec 8))
    (hfit : BitVec.ult (20 : Word) (endPtr - cursor) = true) :
    rlpItemDecode bytes off cursor endPtr
      ((cursor + signExtend12 (1 : BitVec 12)) + (20 : Word)) (20 : Word) := by
  refine ⟨(0x94 : BitVec 8), ?_, Or.inr (Or.inl ?_)⟩
  · rw [List.getElem?_eq_getElem hoff, hb]
  · have hge : ¬ BitVec.ult ((0x94 : BitVec 8).zeroExtend 64) (0x80 : Word) = true := by
      decide
    have hlt : BitVec.ult ((0x94 : BitVec 8).zeroExtend 64) (0xb8 : Word) = true := by
      decide
    have hlen20 : (0x94 : BitVec 8).zeroExtend 64 - (0x80 : Word) = (20 : Word) := by
      decide
    refine ⟨hge, hlt, ?_, ?_, ?_, ?_⟩
    · intro h1
      rw [hlen20] at h1
      exact absurd h1 (by decide)
    · rwa [hlen20]
    · rw [hlen20]
    · exact hlen20

/-- Any successful decode with prefix `0x80` reports `len = 0` (decode-gated hcre). -/
theorem rlpItemDecode_pfx80_imp_len0
    (bytes : List (BitVec 8)) (off : Nat) (cursor endPtr next len : Word)
    (hoff : off < bytes.length)
    (hb : bytes[off]'hoff = (0x80 : BitVec 8))
    (h : rlpItemDecode bytes off cursor endPtr next len) :
    len = (0 : Word) := by
  obtain ⟨b, hb?, hforms⟩ := h
  have heq : b = (0x80 : BitVec 8) := by
    have hget : bytes[off]? = some (bytes[off]'hoff) := List.getElem?_eq_getElem hoff
    rw [hget, hb] at hb?
    exact Option.some.inj hb?.symm
  subst heq
  rcases hforms with h1 | h2 | h3 | h4 | h5
  · have hult : BitVec.ult ((0x80 : BitVec 8).zeroExtend 64) (0x80 : Word) = false := by
      decide
    have : BitVec.ult ((0x80 : BitVec 8).zeroExtend 64) (0x80 : Word) = true := h1.1
    rw [hult] at this
    exact absurd this (by decide)
  · exact h2.2.2.2.2.2
  · have hult : BitVec.ult ((0x80 : BitVec 8).zeroExtend 64) (0xb8 : Word) = true := by
      decide
    have : ¬ BitVec.ult ((0x80 : BitVec 8).zeroExtend 64) (0xb8 : Word) = true := h3.1
    exact absurd hult this
  · have hult : BitVec.ult ((0x80 : BitVec 8).zeroExtend 64) (0xc0 : Word) = true := by
      decide
    have : ¬ BitVec.ult ((0x80 : BitVec 8).zeroExtend 64) (0xc0 : Word) = true := h4.1
    exact absurd hult this
  · have hult : BitVec.ult ((0x80 : BitVec 8).zeroExtend 64) (0xf8 : Word) = true := by
      decide
    have : ¬ BitVec.ult ((0x80 : BitVec 8).zeroExtend 64) (0xf8 : Word) = true := h5.1
    exact absurd hult this

/-- Any successful decode with prefix `0x94` reports `len = 20` (decode-gated hlen20). -/
theorem rlpItemDecode_pfx94_imp_len20
    (bytes : List (BitVec 8)) (off : Nat) (cursor endPtr next len : Word)
    (hoff : off < bytes.length)
    (hb : bytes[off]'hoff = (0x94 : BitVec 8))
    (h : rlpItemDecode bytes off cursor endPtr next len) :
    len = (20 : Word) := by
  obtain ⟨b, hb?, hforms⟩ := h
  have heq : b = (0x94 : BitVec 8) := by
    have hget : bytes[off]? = some (bytes[off]'hoff) := List.getElem?_eq_getElem hoff
    rw [hget, hb] at hb?
    exact Option.some.inj hb?.symm
  subst heq
  rcases hforms with h1 | h2 | h3 | h4 | h5
  · have hult : BitVec.ult ((0x94 : BitVec 8).zeroExtend 64) (0x80 : Word) = false := by
      decide
    have : BitVec.ult ((0x94 : BitVec 8).zeroExtend 64) (0x80 : Word) = true := h1.1
    rw [hult] at this
    exact absurd this (by decide)
  · exact h2.2.2.2.2.2
  · have hult : BitVec.ult ((0x94 : BitVec 8).zeroExtend 64) (0xb8 : Word) = true := by
      decide
    have : ¬ BitVec.ult ((0x94 : BitVec 8).zeroExtend 64) (0xb8 : Word) = true := h3.1
    exact absurd hult this
  · have hult : BitVec.ult ((0x94 : BitVec 8).zeroExtend 64) (0xc0 : Word) = true := by
      decide
    have : ¬ BitVec.ult ((0x94 : BitVec 8).zeroExtend 64) (0xc0 : Word) = true := h4.1
    exact absurd hult this
  · have hult : BitVec.ult ((0x94 : BitVec 8).zeroExtend 64) (0xf8 : Word) = true := by
      decide
    have : ¬ BitVec.ult ((0x94 : BitVec 8).zeroExtend 64) (0xf8 : Word) = true := h5.1
    exact absurd hult this

/-- Decode-gated creation residual: prefix `0x80` ⇒ every decode has `len = 0`. -/
theorem hcre_decode_of_pfx80
    (bytes : List (BitVec 8)) (off : Nat) (cursor endPtr : Word)
    (hoff : off < bytes.length)
    (hb : bytes[off]'hoff = (0x80 : BitVec 8)) :
    ∀ (next len : Word),
      rlpItemDecode bytes off cursor endPtr next len → len = (0 : Word) :=
  fun next len h => rlpItemDecode_pfx80_imp_len0 bytes off cursor endPtr next len hoff hb h

/-- Decode-gated copy residual: prefix `0x94` ⇒ every decode has `len = 20`. -/
theorem hlen20_decode_of_pfx94
    (bytes : List (BitVec 8)) (off : Nat) (cursor endPtr : Word)
    (hoff : off < bytes.length)
    (hb : bytes[off]'hoff = (0x94 : BitVec 8)) :
    ∀ (next len : Word),
      rlpItemDecode bytes off cursor endPtr next len → len = (20 : Word) :=
  fun next len h => rlpItemDecode_pfx94_imp_len20 bytes off cursor endPtr next len hoff hb h

/-- Any successful decode with prefix `0x94` has `next = cursor + 21`
    (content at `cursor+1`, span 20). -/
theorem rlpItemDecode_pfx94_imp_next
    (bytes : List (BitVec 8)) (off : Nat) (cursor endPtr next len : Word)
    (hoff : off < bytes.length)
    (hb : bytes[off]'hoff = (0x94 : BitVec 8))
    (h : rlpItemDecode bytes off cursor endPtr next len) :
    next = cursor + (21 : Word) := by
  obtain ⟨b, hb?, hforms⟩ := h
  have heq : b = (0x94 : BitVec 8) := by
    have hget : bytes[off]? = some (bytes[off]'hoff) := List.getElem?_eq_getElem hoff
    rw [hget, hb] at hb?
    exact Option.some.inj hb?.symm
  subst heq
  rcases hforms with h1 | h2 | h3 | h4 | h5
  · have hult : BitVec.ult ((0x94 : BitVec 8).zeroExtend 64) (0x80 : Word) = false := by
      decide
    have : BitVec.ult ((0x94 : BitVec 8).zeroExtend 64) (0x80 : Word) = true := h1.1
    rw [hult] at this
    exact absurd this (by decide)
  · -- short string: next = (cursor + 1) + (0x94 - 0x80) = cursor + 21
    have hnext : next =
        (cursor + signExtend12 (1 : BitVec 12)) +
          ((0x94 : BitVec 8).zeroExtend 64 - (0x80 : Word)) := h2.2.2.2.2.1
    have h1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    have h20 : (0x94 : BitVec 8).zeroExtend 64 - (0x80 : Word) = (20 : Word) := by decide
    have h21 : (1 : Word) + (20 : Word) = (21 : Word) := by decide
    calc next
        = (cursor + signExtend12 (1 : BitVec 12)) +
            ((0x94 : BitVec 8).zeroExtend 64 - (0x80 : Word)) := hnext
      _ = (cursor + (1 : Word)) + (20 : Word) := by rw [h1, h20]
      _ = cursor + ((1 : Word) + (20 : Word)) := by
          rw [BitVec.add_assoc]
      _ = cursor + (21 : Word) := by rw [h21]
  · have hult : BitVec.ult ((0x94 : BitVec 8).zeroExtend 64) (0xb8 : Word) = true := by
      decide
    have : ¬ BitVec.ult ((0x94 : BitVec 8).zeroExtend 64) (0xb8 : Word) = true := h3.1
    exact absurd hult this
  · have hult : BitVec.ult ((0x94 : BitVec 8).zeroExtend 64) (0xc0 : Word) = true := by
      decide
    have : ¬ BitVec.ult ((0x94 : BitVec 8).zeroExtend 64) (0xc0 : Word) = true := h4.1
    exact absurd hult this
  · have hult : BitVec.ult ((0x94 : BitVec 8).zeroExtend 64) (0xf8 : Word) = true := by
      decide
    have : ¬ BitVec.ult ((0x94 : BitVec 8).zeroExtend 64) (0xf8 : Word) = true := h5.1
    exact absurd hult this

/-- Decode-gated content-pointer residual: prefix `0x94` and
    `contentPtr = cursor + 1` ⇒ every decode has `next = contentPtr + 20`. -/
theorem hnext_content_decode_of_pfx94
    (bytes : List (BitVec 8)) (off : Nat) (cursor endPtr contentPtr : Word)
    (hoff : off < bytes.length)
    (hb : bytes[off]'hoff = (0x94 : BitVec 8))
    (hcontent : contentPtr = cursor + (1 : Word)) :
    ∀ (next len : Word),
      rlpItemDecode bytes off cursor endPtr next len →
        next = contentPtr + (20 : Word) := by
  intro next len h
  have hnext : next = cursor + (21 : Word) :=
    rlpItemDecode_pfx94_imp_next bytes off cursor endPtr next len hoff hb h
  have h21 : (1 : Word) + (20 : Word) = (21 : Word) := by decide
  calc next
      = cursor + (21 : Word) := hnext
    _ = cursor + ((1 : Word) + (20 : Word)) := by rw [h21]
    _ = (cursor + (1 : Word)) + (20 : Word) := by rw [← BitVec.add_assoc]
    _ = contentPtr + (20 : Word) := by rw [hcontent]

/-- Empty bytes item encodes as the single prefix `0x80`. -/
theorem encode_bytes_empty : encode (.bytes []) = [BitVec.ofNat 8 0x80] := by
  have h : (0 : Nat) ≤ 55 := by decide
  simp only [encode, encodeBytes, List.length_nil, h, ↓reduceIte]
  rfl

/-- Successful creation path: `to` field is empty bytes (encode prefix `0x80`). -/
theorem extractSuccess_creation_encode_empty
    (txBytes : List (BitVec 8)) (h : extractSuccess txBytes)
    (hcre : (teerExtractToAddress txBytes).2.2 = (1 : Word)) :
    ∃ items,
      decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
        some items ∧
      items[toFieldIndex (teerTxTypeDispatch txBytes).2.1.toNat]? =
        some (.bytes []) ∧
      encode (.bytes []) = [BitVec.ofNat 8 0x80] := by
  obtain ⟨items, content, hdec, hitem, hcases⟩ := extractSuccess_to_field txBytes h
  rcases hcases with ⟨hnil, _hisCre⟩ | ⟨_, hisCre0⟩
  · subst hnil
    exact ⟨items, hdec, hitem, encode_bytes_empty⟩
  · exact absurd (hcre.symm.trans hisCre0) (by decide)

/-- Successful `decodeListItems` recovers the canonical list encoding. -/
theorem decodeListItems_eq_encode (bs : List Byte) (items : List RLPItem)
    (h : decodeListItems bs = some items) :
    bs = encode (.list items) := by
  simp only [decodeListItems] at h
  match hdec : decode bs with
  | none =>
    simp only [hdec] at h
    cases h
  | some (.bytes _, _) =>
    simp only [hdec] at h
    cases h
  | some (.list its, rest) =>
    simp only [hdec] at h
    match hrest : rest with
    | [] =>
      simp only [List.isEmpty_nil, ↓reduceIte] at h
      have hits : its = items := Option.some.inj h
      rw [← hits]
      simpa using decode_eq_some_imp_encode bs (.list its) [] hdec
    | _ :: _ =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at h
      cases h

/-- Short-form list encode length (via Properties `encode_list_short`). -/
theorem encode_list_short_length (items : List RLPItem)
    (hshort : (encode.encodeItems items).length ≤ 55) :
    (encode (.list items)).length =
      1 + (encode.encodeItems items).length := by
  rw [encode_list_short items hshort]
  simp only [List.length_cons]
  omega

private theorem ofNat8_C0_add_le55 (n : Nat) (hn : n ≤ 55) :
    (BitVec.ofNat 8 (0xC0 + n)).toNat = 0xC0 + n := by
  have hsum : 0xC0 + n < 256 := by omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsum]

private theorem zeroExtend_ofNat8_C0 (n : Nat) (hn : n ≤ 55) :
    ((BitVec.ofNat 8 (0xC0 + n)).zeroExtend 64).toNat = 0xC0 + n := by
  rw [toNat_zeroExtend_byte, ofNat8_C0_add_le55 n hn]

private theorem not_ult_C0_of_pfx_short (n : Nat) (hn : n ≤ 55) :
    ¬ BitVec.ult ((BitVec.ofNat 8 (0xC0 + n)).zeroExtend 64) (0xc0 : Word) = true := by
  intro hult
  have hlt := (BitVec.ult_iff_lt).mp hult
  have hze := zeroExtend_ofNat8_C0 n hn
  have hb : (0xc0 : Word).toNat = 192 := by decide
  rw [BitVec.lt_def, hze, hb] at hlt
  omega

private theorem ult_F8_of_pfx_short (n : Nat) (hn : n ≤ 55) :
    BitVec.ult ((BitVec.ofNat 8 (0xC0 + n)).zeroExtend 64) (0xf8 : Word) = true := by
  apply (BitVec.ult_iff_lt).mpr
  have hze := zeroExtend_ofNat8_C0 n hn
  have hb : (0xf8 : Word).toNat = 248 := by decide
  rw [BitVec.lt_def, hze, hb]
  omega

private theorem pfx_sub_C0_add1 (n : Nat) (hn : n ≤ 55) :
    (((BitVec.ofNat 8 (0xC0 + n)).zeroExtend 64 - (0xc0 : Word)) +
      signExtend12 (1 : BitVec 12)).toNat = n + 1 := by
  have hze := zeroExtend_ofNat8_C0 n hn
  have hse : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hb : (0xc0 : Word).toNat = 192 := by decide
  rw [hse]
  have hle : (0xc0 : Word) ≤ (BitVec.ofNat 8 (0xC0 + n)).zeroExtend 64 := by
    exact (BitVec.le_def).mpr (by rw [hze, hb]; omega)
  have hsub :
      ((BitVec.ofNat 8 (0xC0 + n)).zeroExtend 64 - (0xc0 : Word)).toNat = n := by
    rw [BitVec.toNat_sub_of_le hle, hze, hb]
    omega
  have hlt : n + 1 < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, hsub]
  exact Nat.mod_eq_of_lt hlt

/-- Successful short-list decode ⇒ walk_init short-success pure facts (offset 0). -/
theorem decodeListItems_short_walkInit_guards
    (bs : List Byte) (items : List RLPItem)
    (h : decodeListItems bs = some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hoff : 0 < bs.length) :
    let pfx := bs[0]'hoff
    let listLen := bs.length
    listLen ≠ 0 ∧
      ¬ BitVec.ult (pfx.zeroExtend 64) (0xc0 : Word) = true ∧
      BitVec.ult (pfx.zeroExtend 64) (0xf8 : Word) = true ∧
      ((pfx.zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)).toNat =
        listLen := by
  have henc := decodeListItems_eq_encode bs items h
  have hstr := encode_list_short items hshort
  have hlen := encode_list_short_length items hshort
  have hbs : bs =
      BitVec.ofNat 8 (0xC0 + (encode.encodeItems items).length) ::
        encode.encodeItems items := by
    rw [← hstr, ← henc]
  have hpfx : bs[0]'hoff =
      BitVec.ofNat 8 (0xC0 + (encode.encodeItems items).length) := by
    simp only [hbs, List.getElem_cons_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hz; omega
  · simp only [hpfx]; exact not_ult_C0_of_pfx_short _ hshort
  · simp only [hpfx]; exact ult_F8_of_pfx_short _ hshort
  · simp only [hpfx]
    have h1 := pfx_sub_C0_add1 (encode.encodeItems items).length hshort
    have h2 : bs.length = 1 + (encode.encodeItems items).length := by
      rw [henc, hlen]
    omega

/-- Success ⇒ inner RLP is the encode of its decoded list items. -/
theorem extractSuccess_inner_eq_encode
    (txBytes : List (BitVec 8)) (h : extractSuccess txBytes) :
    ∃ items,
      decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
        some items ∧
      txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat = encode (.list items) := by
  obtain ⟨items, hdec⟩ := extractSuccess_decode txBytes h
  exact ⟨items, hdec, decodeListItems_eq_encode _ _ hdec⟩

/-- `lenW - innerW` as Word matches drop length when bounds hold. -/
theorem listLen_word_eq_drop
    (txBytes : List (BitVec 8)) (lenW innerW : Word)
    (hinner : innerW.toNat < txBytes.length)
    (hlenW : lenW.toNat = txBytes.length) :
    (lenW - innerW).toNat =
      (txBytes.drop innerW.toNat).length := by
  have hle : innerW ≤ lenW := by
    exact (BitVec.le_def).mpr (by omega)
  rw [BitVec.toNat_sub_of_le hle, hlenW, List.length_drop]

/-- Nat equality of `(pfx−0xc0)+1` lifts to Word equality with `listLen`. -/
theorem short_pfx_add1_eq_listLen
    (listLen : Word) (pfx : BitVec 8)
    (hNat : ((pfx.zeroExtend 64 - (0xc0 : Word)) +
        signExtend12 (1 : BitVec 12)).toNat = listLen.toNat) :
    (pfx.zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12) = listLen := by
  apply BitVec.eq_of_toNat_eq
  exact hNat

/-- `h_exact` form for `rlp_walk_init_short_spec_within`. -/
theorem short_walkInit_h_exact
    (listBase listLen : Word) (listOff : Nat) (pfx : BitVec 8)
    (heq : (pfx.zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12) = listLen) :
    (listBase + BitVec.ofNat 64 listOff) +
        ((pfx.zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)) =
      (listBase + BitVec.ofNat 64 listOff) + listLen := by
  rw [heq]

/-- Success + short-list ⇒ walk_init short-success pure (Word-level).
    Residual long-list (≥56 payload) still open. -/
theorem extractSuccess_short_walkInit_guards
    (txBytes : List (BitVec 8)) (lenW : Word)
    (h : extractSuccess txBytes)
    (hlenW : lenW.toNat = txBytes.length)
    (items : List RLPItem)
    (hdec : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55) :
    let innerW := (teerTxTypeDispatch txBytes).2.2
    let listOff := innerW.toNat
    let listLen := lenW - innerW
    listOff < txBytes.length ∧
      listLen ≠ (0 : Word) ∧
      (∃ hoff : listOff < txBytes.length,
        ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
        BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
        ((txBytes[listOff]'hoff).zeroExtend 64 - (0xc0 : Word) +
          signExtend12 (1 : BitVec 12) = listLen)) := by
  let innerW := (teerTxTypeDispatch txBytes).2.2
  let listOff := innerW.toNat
  let listLen := lenW - innerW
  let bs := txBytes.drop listOff
  have hinner : listOff < txBytes.length := extractSuccess_inner_lt txBytes h
  have hlenDrop : listLen.toNat = bs.length :=
    listLen_word_eq_drop txBytes lenW innerW hinner hlenW
  have hoff0 : 0 < bs.length := by
    have hne := decodeListItems_some_ne_nil hdec
    exact List.length_pos_of_ne_nil hne
  have hguards := decodeListItems_short_walkInit_guards bs items hdec hshort hoff0
  have hbs0 : bs[0]'hoff0 = txBytes[listOff]'hinner := by
    simp only [bs]
    have heq := List.getElem_drop (xs := txBytes) (i := listOff) (j := 0) (h := hoff0)
    -- heq: (drop listOff)[0] = txBytes[listOff + 0]
    refine Eq.trans heq ?_
    simp only [Nat.add_zero]
  refine ⟨hinner, ?_, ⟨hinner, ?_, ?_, ?_⟩⟩
  · intro hz
    have hzN : listLen.toNat = 0 := by
      change (lenW - innerW).toNat = 0
      rw [hz]
      exact BitVec.toNat_zero
    have : bs.length ≠ 0 := Nat.ne_of_gt hoff0
    exact this (by rw [← hlenDrop, hzN])
  · have hg := hguards.2.1
    simpa only [hbs0] using hg
  · have hg := hguards.2.2.1
    simpa only [hbs0] using hg
  · have hNat := hguards.2.2.2
    have hNat' :
        (((txBytes[listOff]'hinner).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)).toNat = listLen.toNat := by
      simpa only [hbs0, hlenDrop] using hNat
    exact short_pfx_add1_eq_listLen listLen (txBytes[listOff]'hinner) hNat'

/-- Package Front short walk_init hyps from extractSuccess + short list.
    Discharges `hlistLen_ne` / `h_ge` / `h_hi` / `h_exact` shape used by
    `extractFrontToAfterSave_short`. -/
theorem extractSuccess_short_front_walkInit_hyps
    (txBase lenW : Word) (txBytes : List (BitVec 8))
    (h : extractSuccess txBytes)
    (hlenW : lenW.toNat = txBytes.length)
    (items : List RLPItem)
    (hdec : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55) :
    let innerW := (teerTxTypeDispatch txBytes).2.2
    let hoff : innerW.toNat < txBytes.length := extractSuccess_inner_lt txBytes h
    (lenW - innerW) ≠ (0 : Word) ∧
      ¬ BitVec.ult ((txBytes[innerW.toNat]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
      BitVec.ult ((txBytes[innerW.toNat]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
      ((txBase + BitVec.ofNat 64 innerW.toNat) +
          (((txBytes[innerW.toNat]'hoff).zeroExtend 64 - (0xc0 : Word)) +
            signExtend12 (1 : BitVec 12)) =
        (txBase + BitVec.ofNat 64 innerW.toNat) + (lenW - innerW)) := by
  have hg := extractSuccess_short_walkInit_guards txBytes lenW h hlenW items hdec hshort
  obtain ⟨_hinner, hne, ⟨hoff', hge, hhi, heq⟩⟩ := hg
  refine ⟨hne, ?_, ?_, ?_⟩
  · convert hge
  · convert hhi
  · exact short_walkInit_h_exact txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
      (teerTxTypeDispatch txBytes).2.2.toNat
      (txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff') heq

/-! ## encodeItems offset algebra (walk_next cursor chain) -/

/-- Byte length of the encoding of the first `n` list items. -/
def encodeItemsPrefixLen (items : List RLPItem) (n : Nat) : Nat :=
  (encode.encodeItems (items.take n)).length

theorem encodeItems_nil : encode.encodeItems ([] : List RLPItem) = [] := rfl

theorem encodeItems_cons (item : RLPItem) (rest : List RLPItem) :
    encode.encodeItems (item :: rest) = encode item ++ encode.encodeItems rest := rfl

/-- Payload offset of item `0` is 0. -/
theorem encodeItemsPrefixLen_zero (items : List RLPItem) :
    encodeItemsPrefixLen items 0 = 0 := by
  simp only [encodeItemsPrefixLen, List.take_zero, encodeItems_nil, List.length_nil]

private theorem encodeItems_append_singleton (xs : List RLPItem) (item : RLPItem) :
    encode.encodeItems (xs ++ [item]) =
      encode.encodeItems xs ++ encode item := by
  induction xs with
  | nil => simp [encodeItems_nil, encodeItems_cons]
  | cons x rest ih =>
    simp only [List.cons_append, encodeItems_cons, ih, List.append_assoc]

private theorem take_succ_eq_append_get {α : Type _} (l : List α) (n : Nat)
    (hn : n < l.length) :
    l.take (n + 1) = l.take n ++ [l[n]'hn] := by
  induction l generalizing n with
  | nil => cases hn
  | cons a as ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.take_succ_cons, List.getElem_cons_succ]
      have hn' : n < as.length := Nat.lt_of_succ_lt_succ hn
      rw [ih n hn', List.cons_append]

/-- Prefix length advances by one encoded item. -/
theorem encodeItemsPrefixLen_succ (items : List RLPItem) (n : Nat)
    (hn : n < items.length) :
    encodeItemsPrefixLen items (n + 1) =
      encodeItemsPrefixLen items n + (encode (items[n]'hn)).length := by
  unfold encodeItemsPrefixLen
  have htake := take_succ_eq_append_get items n hn
  rw [htake, encodeItems_append_singleton, List.length_append]

/-- Absolute short-list field offset: `listOff + 1 + prefixLen`. -/
def shortListSrcOff (listOff : Nat) (items : List RLPItem) (k : Nat) : Nat :=
  listOff + 1 + encodeItemsPrefixLen items k

theorem shortListSrcOff_zero (listOff : Nat) (items : List RLPItem) :
    shortListSrcOff listOff items 0 = listOff + 1 := by
  simp only [shortListSrcOff, encodeItemsPrefixLen_zero, Nat.add_zero]

theorem shortListSrcOff_succ (listOff : Nat) (items : List RLPItem) (n : Nat)
    (hn : n < items.length) :
    shortListSrcOff listOff items (n + 1) =
      shortListSrcOff listOff items n + (encode (items[n]'hn)).length := by
  simp only [shortListSrcOff, encodeItemsPrefixLen_succ items n hn]
  omega

/-- Short-string decode reports `next = cursor + 1 + len` (Word). -/
theorem rlpItemDecode_short_string_next
    (bytes : List (BitVec 8)) (off : Nat) (cursor endPtr next len : Word)
    (h : rlpItemDecode bytes off cursor endPtr next len)
    (hb : ∃ b : BitVec 8, bytes[off]? = some b ∧
      ¬ BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true ∧
      BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true) :
    next = (cursor + signExtend12 (1 : BitVec 12)) + len := by
  obtain ⟨b, hb?, hforms⟩ := h
  obtain ⟨b', hb?', hge, hlt⟩ := hb
  have heq : b = b' := by
    have : some b = some b' := hb?.symm.trans hb?'
    exact Option.some.inj this
  subst heq
  rcases hforms with h1 | h2 | h3 | h4 | h5
  · exact absurd h1.1 hge
  · have hlen : len = b.zeroExtend 64 - (0x80 : Word) := h2.2.2.2.2.2
    have hnext' :
        next = (cursor + signExtend12 (1 : BitVec 12)) +
          (b.zeroExtend 64 - (0x80 : Word)) := h2.2.2.2.2.1
    rwa [← hlen] at hnext'
  · exact absurd hlt h3.1
  · have hb8 : (0xb8 : Word).toNat = 0xb8 := by decide
    have hc0 : (0xc0 : Word).toNat = 0xc0 := by decide
    have hlt' : (b.zeroExtend 64).toNat < 0xb8 := by
      have := (BitVec.ult_iff_lt).1 hlt
      simpa [BitVec.lt_def, hb8] using this
    have hult : BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true :=
      (BitVec.ult_iff_lt).2 (by
        have : (b.zeroExtend 64).toNat < 0xc0 := by omega
        simpa [BitVec.lt_def, hc0] using this)
    exact absurd hult h4.1
  · have hb8 : (0xb8 : Word).toNat = 0xb8 := by decide
    have hf8 : (0xf8 : Word).toNat = 0xf8 := by decide
    have hlt' : (b.zeroExtend 64).toNat < 0xb8 := by
      have := (BitVec.ult_iff_lt).1 hlt
      simpa [BitVec.lt_def, hb8] using this
    have hult : BitVec.ult (b.zeroExtend 64) (0xf8 : Word) = true :=
      (BitVec.ult_iff_lt).2 (by
        have : (b.zeroExtend 64).toNat < 0xf8 := by omega
        simpa [BitVec.lt_def, hf8] using this)
    exact absurd hult h5.1

/-- Decode-gated hnext for short-string fields: next lands at `srcOff + 1 + len.toNat`
    when cursor is `txBase+srcOff` and no wrap. -/
theorem hnext_short_string_of_decode
    (txBytes : List (BitVec 8)) (txBase : Word) (srcOff : Nat)
    (endPtr next len : Word)
    (hover : txBase.toNat + srcOff < 2 ^ 64)
    (hdec : rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
      endPtr next len)
    (hb : ∃ b : BitVec 8, txBytes[srcOff]? = some b ∧
      ¬ BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true ∧
      BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true)
    (hspan : txBase.toNat + srcOff + 1 + len.toNat < 2 ^ 64) :
    next = txBase + BitVec.ofNat 64 (srcOff + 1 + len.toNat) := by
  have hnext := rlpItemDecode_short_string_next txBytes srcOff
    (txBase + BitVec.ofNat 64 srcOff) endPtr next len hdec hb
  have hse : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  rw [hse] at hnext
  have hcalc :
      (txBase + BitVec.ofNat 64 srcOff) + (1 : Word) + len =
        txBase + BitVec.ofNat 64 (srcOff + 1 + len.toNat) := by
    apply BitVec.eq_of_toNat_eq
    have h1 : ((1 : Word).toNat) = 1 := by decide
    have hsrc' : srcOff < 2 ^ 64 := by omega
    have hsrc'' : (BitVec.ofNat 64 srcOff).toNat = srcOff := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsrc']
    have htb : (txBase + BitVec.ofNat 64 srcOff).toNat = txBase.toNat + srcOff := by
      rw [BitVec.toNat_add, hsrc'']
      omega
    have hl1 : ((txBase + BitVec.ofNat 64 srcOff) + (1 : Word)).toNat =
        txBase.toNat + srcOff + 1 := by
      rw [BitVec.toNat_add, htb, h1]
      omega
    have hl : (((txBase + BitVec.ofNat 64 srcOff) + (1 : Word)) + len).toNat =
        txBase.toNat + srcOff + 1 + len.toNat := by
      rw [BitVec.toNat_add, hl1]
      have : len.toNat < 2 ^ 64 := len.isLt
      omega
    have hr : (txBase + BitVec.ofNat 64 (srcOff + 1 + len.toNat)).toNat =
        txBase.toNat + (srcOff + 1 + len.toNat) := by
      have hoff : srcOff + 1 + len.toNat < 2 ^ 64 := by omega
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff]
      omega
    omega
  exact hnext.trans hcalc

/-- Split `encodeItems` at an index. -/
theorem encodeItems_take_drop (items : List RLPItem) (n : Nat) :
    encode.encodeItems items =
      encode.encodeItems (items.take n) ++ encode.encodeItems (items.drop n) := by
  induction items generalizing n with
  | nil =>
    cases n <;> simp [encodeItems_nil]
  | cons item rest ih =>
    cases n with
    | zero =>
      simp only [List.take_zero, List.drop_zero, encodeItems_nil, List.nil_append]
    | succ n =>
      simp only [List.take_succ_cons, List.drop_succ_cons, encodeItems_cons]
      rw [ih n, List.append_assoc]

/-- Encoding of item `n` sits at offset `encodeItemsPrefixLen items n` in the payload. -/
theorem encodeItems_drop_at (items : List RLPItem) (n : Nat) (hn : n < items.length) :
    (encode.encodeItems items).drop (encodeItemsPrefixLen items n) =
      encode (items[n]'hn) ++ encode.encodeItems (items.drop (n + 1)) := by
  have hsplit := encodeItems_take_drop items n
  have hdropn : items.drop n = items[n]'hn :: items.drop (n + 1) :=
    List.drop_eq_getElem_cons hn
  unfold encodeItemsPrefixLen
  -- LHS: drop (len take) (take ++ drop) = drop
  have hlen : (encode.encodeItems (items.take n)).length =
      (encode.encodeItems (items.take n)).length := rfl
  calc (encode.encodeItems items).drop (encode.encodeItems (items.take n)).length
      = (encode.encodeItems (items.take n) ++ encode.encodeItems (items.drop n)).drop
          (encode.encodeItems (items.take n)).length := by rw [hsplit]
    _ = encode.encodeItems (items.drop n) := List.drop_left' rfl
    _ = encode.encodeItems (items[n]'hn :: items.drop (n + 1)) := by rw [hdropn]
    _ = encode (items[n]'hn) ++ encode.encodeItems (items.drop (n + 1)) := encodeItems_cons _ _

/-- Short-list encoding: payload starts after the 1-byte prefix. -/
theorem encode_list_short_drop_payload (items : List RLPItem)
    (hshort : (encode.encodeItems items).length ≤ 55) :
    (encode (.list items)).drop 1 = encode.encodeItems items := by
  have henc := encode_list_short items hshort
  rw [henc]
  rfl

/-- Full-buffer form: item `n` of a short list at `listOff` begins at
    `listOff + 1 + encodeItemsPrefixLen items n`. -/
theorem short_list_item_drop
    (bs : List Byte) (listOff : Nat) (items : List RLPItem) (n : Nat)
    (henc : bs.drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : n < items.length) :
    bs.drop (listOff + 1 + encodeItemsPrefixLen items n) =
      encode (items[n]'hn) ++ encode.encodeItems (items.drop (n + 1)) := by
  have hpay' : bs.drop (listOff + 1) = encode.encodeItems items := by
    have : (bs.drop listOff).drop 1 = encode.encodeItems items := by
      rw [henc, encode_list_short_drop_payload items hshort]
    -- (drop listOff).drop 1 = drop (1+listOff) = drop (listOff+1)
    simpa [List.drop_drop, Nat.add_comm] using this
  have hitem := encodeItems_drop_at items n hn
  let p := encodeItemsPrefixLen items n
  -- drop_drop: drop n (drop m l) = drop (m + n) l
  have hdd : List.drop p (List.drop (listOff + 1) bs) =
      List.drop (listOff + 1 + p) bs := by
    simp [List.drop_drop, Nat.add_assoc]
  calc bs.drop (listOff + 1 + p)
      = List.drop p (List.drop (listOff + 1) bs) := hdd.symm
    _ = (encode.encodeItems items).drop p := by rw [hpay']
    _ = encode (items[n]'hn) ++ encode.encodeItems (items.drop (n + 1)) := hitem

/-- If `bs.drop off = b :: rest` then `off < length` and `bs[off] = b`. -/
theorem getElem_of_drop_cons (bs : List Byte) (off : Nat) (b : Byte) (rest : List Byte)
    (h : bs.drop off = b :: rest) :
    ∃ hoff : off < bs.length, bs[off]'hoff = b := by
  have hpos : 0 < (bs.drop off).length := by rw [h]; simp
  have hoff : off < bs.length := by
    rw [List.length_drop] at hpos
    omega
  refine ⟨hoff, ?_⟩
  have heq := List.getElem_drop (xs := bs) (i := off) (j := 0) (h := by
    rw [List.length_drop]; omega)
  have h0 : (bs.drop off)[0]'(by rw [h]; simp) = b := by simp [h]
  have : bs[off + 0]'(by omega) = b := heq.symm.trans h0
  simpa using this

/-- Empty-bytes item at absolute offset from short-list placement. -/
theorem short_list_empty_bytes_pfx
    (bs : List Byte) (listOff : Nat) (items : List RLPItem) (n : Nat)
    (henc : bs.drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : n < items.length)
    (hitem : items[n]'hn = .bytes []) :
    let off := listOff + 1 + encodeItemsPrefixLen items n
    ∃ hoff : off < bs.length, bs[off]'hoff = (0x80 : BitVec 8) := by
  intro off
  have hdrop := short_list_item_drop bs listOff items n henc hshort hn
  have hencI : encode (items[n]'hn) = [BitVec.ofNat 8 0x80] := by
    rw [hitem, encode_bytes_empty]
  have hdrop' :
      bs.drop off = BitVec.ofNat 8 0x80 :: encode.encodeItems (items.drop (n + 1)) := by
    simpa [off, hencI] using hdrop
  obtain ⟨hoff, hb⟩ := getElem_of_drop_cons bs off (BitVec.ofNat 8 0x80) _ hdrop'
  exact ⟨hoff, hb⟩

/-- Creation + type234 + short list ⇒ field index 5 is empty bytes at computable `0x80` offset. -/
theorem extractSuccess_creation_type234_field5_pfx80
    (txBytes : List (BitVec 8))
    (h : extractSuccess txBytes)
    (hcreFlag : (teerExtractToAddress txBytes).2.2 = (1 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch txBytes).2.1.toNat)
    (items : List RLPItem)
    (hdec : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55) :
    let listOff := (teerTxTypeDispatch txBytes).2.2.toNat
    let off := listOff + 1 + encodeItemsPrefixLen items 5
    (5 : Nat) < items.length ∧
      items[5]? = some (.bytes []) ∧
      ∃ hoff : off < txBytes.length, txBytes[off]'hoff = (0x80 : BitVec 8) := by
  intro listOff off
  have hidx := extractSuccess_type234_toFieldIndex txBytes h hge
  have htf := extractSuccess_creation_encode_empty txBytes h hcreFlag
  obtain ⟨items', hdec', hitem, _henc80⟩ := htf
  have hitems : items = items' := by
    have : some items = some items' := hdec.symm.trans hdec'
    exact Option.some.inj this
  subst hitems
  have h5 : toFieldIndex (teerTxTypeDispatch txBytes).2.1.toNat = 5 := hidx
  have hget : items[5]? = some (.bytes []) := by simpa [h5] using hitem
  have hn : (5 : Nat) < items.length := (List.getElem?_eq_some_iff.mp hget).1
  have hval : items[5]'hn = .bytes [] := (List.getElem?_eq_some_iff.mp hget).2
  have hencFull := decodeListItems_eq_encode _ _ hdec
  have hpfx := short_list_empty_bytes_pfx txBytes listOff items 5 hencFull hshort hn hval
  exact ⟨hn, hget, hpfx⟩

/-- Packaging `hcre` for creation type234 short: when `srcOff5` is the field-5
    prefix offset, every successful walk_next decode has `len = 0`. -/
theorem extractSuccess_creation_type234_hcre
    (txBytes : List (BitVec 8)) (txBase : Word) (srcOff5 : Nat)
    (h : extractSuccess txBytes)
    (hcreFlag : (teerExtractToAddress txBytes).2.2 = (1 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch txBytes).2.1.toNat)
    (items : List RLPItem)
    (hdecL : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hsrc : srcOff5 =
      (teerTxTypeDispatch txBytes).2.2.toNat + 1 + encodeItemsPrefixLen items 5) :
    ∀ (endPtr next5 len5 : Word),
      rlpItemDecode txBytes srcOff5 (txBase + BitVec.ofNat 64 srcOff5)
        endPtr next5 len5 → len5 = (0 : Word) := by
  have hf := extractSuccess_creation_type234_field5_pfx80 txBytes h hcreFlag hge
    items hdecL hshort
  obtain ⟨_hn, _hget, hpfx⟩ := hf
  obtain ⟨hoff, hb⟩ := hpfx
  have hsrc' : srcOff5 =
      (teerTxTypeDispatch txBytes).2.2.toNat + 1 + encodeItemsPrefixLen items 5 := hsrc
  intro endPtr next5 len5 hdec
  have hoff' : srcOff5 < txBytes.length := by
    simpa [hsrc'] using hoff
  have hb' : txBytes[srcOff5]'hoff' = (0x80 : BitVec 8) := by
    simpa [hsrc'] using hb
  exact hcre_decode_of_pfx80 txBytes srcOff5
    (txBase + BitVec.ofNat 64 srcOff5) endPtr hoff' hb' next5 len5 hdec

/-- Fit-gated `hdec5` for empty short field: prefix `0x80` + room for header
    ⇒ ∃ next,len with `rlpItemDecode` (honest replacement for universal ∃decode). -/
theorem hdec_empty_short_of_pfx80
    (bytes : List (BitVec 8)) (off : Nat) (cursor endPtr : Word)
    (hoff : off < bytes.length)
    (hb : bytes[off]'hoff = (0x80 : BitVec 8))
    (hfit : BitVec.ult (0 : Word) (endPtr - cursor) = true) :
    ∃ next len : Word, rlpItemDecode bytes off cursor endPtr next len :=
  ⟨cursor + signExtend12 (1 : BitVec 12), (0 : Word),
    rlpItemDecode_empty_short bytes off cursor endPtr hoff hb hfit⟩

/-- Creation type234 short: field-5 offset + fit ⇒ packaging-shaped ∃decode. -/
theorem extractSuccess_creation_type234_hdec5
    (txBytes : List (BitVec 8)) (txBase endPtr : Word) (srcOff5 : Nat)
    (h : extractSuccess txBytes)
    (hcreFlag : (teerExtractToAddress txBytes).2.2 = (1 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch txBytes).2.1.toNat)
    (items : List RLPItem)
    (hdecL : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hsrc : srcOff5 =
      (teerTxTypeDispatch txBytes).2.2.toNat + 1 + encodeItemsPrefixLen items 5)
    (hfit : BitVec.ult (0 : Word)
      (endPtr - (txBase + BitVec.ofNat 64 srcOff5)) = true) :
    ∃ next5 len5 : Word,
      rlpItemDecode txBytes srcOff5 (txBase + BitVec.ofNat 64 srcOff5)
        endPtr next5 len5 := by
  have hf := extractSuccess_creation_type234_field5_pfx80 txBytes h hcreFlag hge
    items hdecL hshort
  obtain ⟨_hn, _hget, hpfx⟩ := hf
  obtain ⟨hoff, hb⟩ := hpfx
  have hsrc' : srcOff5 =
      (teerTxTypeDispatch txBytes).2.2.toNat + 1 + encodeItemsPrefixLen items 5 := hsrc
  have hoff' : srcOff5 < txBytes.length := by
    simpa [hsrc'] using hoff
  have hb' : txBytes[srcOff5]'hoff' = (0x80 : BitVec 8) := by
    simpa [hsrc'] using hb
  exact hdec_empty_short_of_pfx80 txBytes srcOff5
    (txBase + BitVec.ofNat 64 srcOff5) endPtr hoff' hb' hfit

/-- Empty bytes encode has length 1. -/
theorem encode_bytes_empty_length : (encode (.bytes [])).length = 1 := by
  rw [encode_bytes_empty]; rfl

/-- Short-list offset advances by 1 across an empty-bytes field. -/
theorem shortListSrcOff_succ_empty
    (listOff : Nat) (items : List RLPItem) (n : Nat) (hn : n < items.length)
    (hitem : items[n]'hn = .bytes []) :
    shortListSrcOff listOff items (n + 1) =
      shortListSrcOff listOff items n + 1 := by
  have h := shortListSrcOff_succ listOff items n hn
  have hl : (encode (items[n]'hn)).length = 1 := by
    rw [hitem, encode_bytes_empty_length]
  rwa [hl] at h

/-- Prefix `0x80` decode ⇒ `next = cursor + 1`. -/
theorem rlpItemDecode_pfx80_imp_next
    (bytes : List (BitVec 8)) (off : Nat) (cursor endPtr next len : Word)
    (hoff : off < bytes.length)
    (hb : bytes[off]'hoff = (0x80 : BitVec 8))
    (h : rlpItemDecode bytes off cursor endPtr next len) :
    next = cursor + signExtend12 (1 : BitVec 12) := by
  have hlen0 := rlpItemDecode_pfx80_imp_len0 bytes off cursor endPtr next len hoff hb h
  have hb' : ∃ b : BitVec 8, bytes[off]? = some b ∧
      ¬ BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true ∧
      BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true := by
    refine ⟨(0x80 : BitVec 8), ?_, by decide, by decide⟩
    rw [List.getElem?_eq_getElem hoff, hb]
  have hnext := rlpItemDecode_short_string_next bytes off cursor endPtr next len h hb'
  rw [hlen0] at hnext
  -- next = cursor + se1 + 0
  simpa [BitVec.add_zero] using hnext

/-- Decode-gated packaging hnext for empty short field at `srcOff`:
    every successful decode has `next = txBase + (srcOff + 1)`. -/
theorem hnext_empty_short_of_pfx80
    (txBytes : List (BitVec 8)) (txBase : Word) (srcOff : Nat)
    (hoff : srcOff < txBytes.length)
    (hb : txBytes[srcOff]'hoff = (0x80 : BitVec 8))
    (_hover : txBase.toNat + srcOff < 2 ^ 64)
    (hspan : txBase.toNat + srcOff + 1 < 2 ^ 64) :
    ∀ (endPtr next len : Word),
      rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
        endPtr next len →
      next = txBase + BitVec.ofNat 64 (srcOff + 1) := by
  intro endPtr next len hdec
  have hnext := rlpItemDecode_pfx80_imp_next txBytes srcOff
    (txBase + BitVec.ofNat 64 srcOff) endPtr next len hoff hb hdec
  have hse : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  rw [hse] at hnext
  have hcalc :
      (txBase + BitVec.ofNat 64 srcOff) + (1 : Word) =
        txBase + BitVec.ofNat 64 (srcOff + 1) := by
    apply BitVec.eq_of_toNat_eq
    have h1 : ((1 : Word).toNat) = 1 := by decide
    have hsrc' : srcOff < 2 ^ 64 := by omega
    have hsrc'' : (BitVec.ofNat 64 srcOff).toNat = srcOff := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsrc']
    have htb : (txBase + BitVec.ofNat 64 srcOff).toNat = txBase.toNat + srcOff := by
      rw [BitVec.toNat_add, hsrc'']; omega
    have hl : ((txBase + BitVec.ofNat 64 srcOff) + (1 : Word)).toNat =
        txBase.toNat + srcOff + 1 := by
      rw [BitVec.toNat_add, htb, h1]; omega
    have hr : (txBase + BitVec.ofNat 64 (srcOff + 1)).toNat =
        txBase.toNat + (srcOff + 1) := by
      have hoff' : srcOff + 1 < 2 ^ 64 := by omega
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff']; omega
    omega
  exact hnext.trans hcalc

/-- Empty field at `shortListSrcOff n` ⇒ decode-gated next is `txBase + shortListSrcOff (n+1)`. -/
theorem hnext_empty_matches_srcOff_succ
    (txBytes : List (BitVec 8)) (txBase : Word) (listOff : Nat)
    (items : List RLPItem) (n : Nat) (hn : n < items.length)
    (hitem : items[n]'hn = .bytes [])
    (henc : txBytes.drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hover : txBase.toNat + shortListSrcOff listOff items n < 2 ^ 64)
    (hspan : txBase.toNat + shortListSrcOff listOff items (n + 1) < 2 ^ 64) :
    let srcOff := shortListSrcOff listOff items n
    let srcOff' := shortListSrcOff listOff items (n + 1)
    ∀ (endPtr next len : Word),
      rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
        endPtr next len →
      next = txBase + BitVec.ofNat 64 srcOff' := by
  intro srcOff srcOff' endPtr next len hdec
  obtain ⟨hoff, hb⟩ :=
    short_list_empty_bytes_pfx txBytes listOff items n henc hshort hn hitem
  have hsucc := shortListSrcOff_succ_empty listOff items n hn hitem
  -- unfold let-bound offsets to concrete Nats for getElem / arithmetic
  have hsrcEq : srcOff = listOff + 1 + encodeItemsPrefixLen items n := rfl
  have hoff' : srcOff < txBytes.length := by simpa [hsrcEq] using hoff
  have hb' : txBytes[srcOff]'hoff' = (0x80 : BitVec 8) := by
    simpa [hsrcEq] using hb
  have hover' : txBase.toNat + srcOff < 2 ^ 64 := by
    simpa [srcOff] using hover
  have hsucc' : srcOff' = srcOff + 1 := by
    simpa [srcOff, srcOff'] using hsucc
  have hspan' : txBase.toNat + srcOff + 1 < 2 ^ 64 := by
    have hsp : txBase.toNat + srcOff' < 2 ^ 64 := by simpa [srcOff'] using hspan
    rwa [hsucc'] at hsp
  have hnext := hnext_empty_short_of_pfx80 txBytes txBase srcOff hoff' hb' hover' hspan'
    endPtr next len hdec
  -- next = txBase + (srcOff+1) = txBase + srcOff'
  rwa [← hsucc'] at hnext

/-- Short bytes (`len ≠ 1`, `≤ 55`) encode length is `1 + data.length`. -/
theorem encode_bytes_short_ne_one_length (data : List Byte)
    (hlen : data.length ≤ 55) (hne1 : data.length ≠ 1) :
    (encode (.bytes data)).length = 1 + data.length := by
  simp only [encode]
  rw [encodeBytes_short_of_length_ne_one data hlen hne1]
  simp [Nat.add_comm]

/-- Single-byte form (`p < 0x80`): encode is the lone byte. -/
theorem encode_bytes_single (b : Byte) (h : b.toNat < 0x80) :
    encode (.bytes [b]) = [b] := by
  simp only [encode, encodeBytes, h, ↓reduceIte]

theorem encode_bytes_single_length (b : Byte) (h : b.toNat < 0x80) :
    (encode (.bytes [b])).length = 1 := by
  rw [encode_bytes_single b h]; rfl

/-- Single-byte decode ⇒ `next = cursor + 1` and `len = 1`. -/
theorem rlpItemDecode_single_byte_next
    (bytes : List (BitVec 8)) (off : Nat) (cursor endPtr next len : Word)
    (hoff : off < bytes.length)
    (hb : (bytes[off]'hoff).toNat < 0x80)
    (h : rlpItemDecode bytes off cursor endPtr next len) :
    next = cursor + signExtend12 (1 : BitVec 12) ∧ len = (1 : Word) := by
  obtain ⟨b, hb?, hforms⟩ := h
  have heq : b = bytes[off]'hoff := by
    have hget : bytes[off]? = some (bytes[off]'hoff) := List.getElem?_eq_getElem hoff
    rw [hget] at hb?
    exact Option.some.inj hb?.symm
  have hult : BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true := by
    have hze : (b.zeroExtend 64).toNat = b.toNat := toNat_zeroExtend_byte b
    have h80 : (0x80 : Word).toNat = 0x80 := by decide
    exact (BitVec.ult_iff_lt).2 (by
      have : (b.zeroExtend 64).toNat < 0x80 := by rw [hze, heq]; exact hb
      simpa [BitVec.lt_def, h80] using this)
  rcases hforms with h1 | h2 | h3 | h4 | h5
  · exact ⟨h1.2.2.1, h1.2.2.2⟩
  · exact absurd hult h2.1
  · have hb8 : BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true := by
      have hze : (b.zeroExtend 64).toNat = b.toNat := toNat_zeroExtend_byte b
      have hb8n : (0xb8 : Word).toNat = 0xb8 := by decide
      exact (BitVec.ult_iff_lt).2 (by
        have : (b.zeroExtend 64).toNat < 0xb8 := by rw [hze, heq]; omega
        simpa [BitVec.lt_def, hb8n] using this)
    exact absurd hb8 h3.1
  · have hc0 : BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true := by
      have hze : (b.zeroExtend 64).toNat = b.toNat := toNat_zeroExtend_byte b
      have hc0n : (0xc0 : Word).toNat = 0xc0 := by decide
      exact (BitVec.ult_iff_lt).2 (by
        have : (b.zeroExtend 64).toNat < 0xc0 := by rw [hze, heq]; omega
        simpa [BitVec.lt_def, hc0n] using this)
    exact absurd hc0 h4.1
  · have hf8 : BitVec.ult (b.zeroExtend 64) (0xf8 : Word) = true := by
      have hze : (b.zeroExtend 64).toNat = b.toNat := toNat_zeroExtend_byte b
      have hf8n : (0xf8 : Word).toNat = 0xf8 := by decide
      exact (BitVec.ult_iff_lt).2 (by
        have : (b.zeroExtend 64).toNat < 0xf8 := by rw [hze, heq]; omega
        simpa [BitVec.lt_def, hf8n] using this)
    exact absurd hf8 h5.1

/-- Decode-gated packaging hnext for single-byte field at `srcOff`. -/
theorem hnext_single_byte_of_pfx
    (txBytes : List (BitVec 8)) (txBase : Word) (srcOff : Nat)
    (hoff : srcOff < txBytes.length)
    (hb : (txBytes[srcOff]'hoff).toNat < 0x80)
    (_hover : txBase.toNat + srcOff < 2 ^ 64)
    (hspan : txBase.toNat + srcOff + 1 < 2 ^ 64) :
    ∀ (endPtr next len : Word),
      rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
        endPtr next len →
      next = txBase + BitVec.ofNat 64 (srcOff + 1) := by
  intro endPtr next len hdec
  have ⟨hnext, _hlen⟩ := rlpItemDecode_single_byte_next txBytes srcOff
    (txBase + BitVec.ofNat 64 srcOff) endPtr next len hoff hb hdec
  have hse : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  rw [hse] at hnext
  have hcalc :
      (txBase + BitVec.ofNat 64 srcOff) + (1 : Word) =
        txBase + BitVec.ofNat 64 (srcOff + 1) := by
    apply BitVec.eq_of_toNat_eq
    have h1 : ((1 : Word).toNat) = 1 := by decide
    have hsrc' : srcOff < 2 ^ 64 := by omega
    have hsrc'' : (BitVec.ofNat 64 srcOff).toNat = srcOff := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsrc']
    have htb : (txBase + BitVec.ofNat 64 srcOff).toNat = txBase.toNat + srcOff := by
      rw [BitVec.toNat_add, hsrc'']; omega
    have hl : ((txBase + BitVec.ofNat 64 srcOff) + (1 : Word)).toNat =
        txBase.toNat + srcOff + 1 := by
      rw [BitVec.toNat_add, htb, h1]; omega
    have hr : (txBase + BitVec.ofNat 64 (srcOff + 1)).toNat =
        txBase.toNat + (srcOff + 1) := by
      have hoff' : srcOff + 1 < 2 ^ 64 := by omega
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff']; omega
    omega
  exact hnext.trans hcalc

#print axioms rlpItemDecode_empty_short
#print axioms rlpWalkNextOk_empty_short
#print axioms rlpItemDecode_addr20_short
#print axioms rlpItemDecode_pfx80_imp_len0
#print axioms rlpItemDecode_pfx94_imp_len20
#print axioms hcre_decode_of_pfx80
#print axioms hlen20_decode_of_pfx94
#print axioms rlpItemDecode_pfx94_imp_next
#print axioms hnext_content_decode_of_pfx94
#print axioms encode_bytes_empty
#print axioms extractSuccess_creation_encode_empty
#print axioms decodeListItems_eq_encode
#print axioms decodeListItems_short_walkInit_guards
#print axioms extractSuccess_inner_eq_encode
#print axioms listLen_word_eq_drop
#print axioms extractSuccess_short_walkInit_guards
#print axioms extractSuccess_short_front_walkInit_hyps
#print axioms encodeItems_take_drop
#print axioms encodeItems_drop_at
#print axioms short_list_item_drop
#print axioms short_list_empty_bytes_pfx
#print axioms extractSuccess_creation_type234_field5_pfx80
#print axioms extractSuccess_creation_type234_hcre
#print axioms hdec_empty_short_of_pfx80
#print axioms extractSuccess_creation_type234_hdec5
#print axioms encodeItemsPrefixLen_zero
#print axioms encodeItemsPrefixLen_succ
#print axioms shortListSrcOff_zero
#print axioms shortListSrcOff_succ
#print axioms rlpItemDecode_short_string_next
#print axioms hnext_short_string_of_decode
#print axioms encode_bytes_empty_length
#print axioms shortListSrcOff_succ_empty
#print axioms rlpItemDecode_pfx80_imp_next
#print axioms hnext_empty_short_of_pfx80
#print axioms hnext_empty_matches_srcOff_succ
#print axioms encode_bytes_short_ne_one_length
#print axioms encode_bytes_single
#print axioms encode_bytes_single_length
#print axioms rlpItemDecode_single_byte_next
#print axioms hnext_single_byte_of_pfx

/-- Each item's encode length is ≤ total `encodeItems` length. -/
theorem encode_item_length_le_encodeItems (items : List RLPItem) (n : Nat)
    (hn : n < items.length) :
    (encode (items[n]'hn)).length ≤ (encode.encodeItems items).length := by
  have hdrop := encodeItems_drop_at items n hn
  have hlen := congrArg List.length hdrop
  simp only [List.length_drop, List.length_append] at hlen
  -- length (drop p xs) = length xs - p, so itemLen ≤ length xs - p ≤ length xs
  have hsub :
      (encode.encodeItems items).length - encodeItemsPrefixLen items n =
        (encode (items[n]'hn)).length +
          (encode.encodeItems (items.drop (n + 1))).length := hlen
  have hle : (encode (items[n]'hn)).length ≤
      (encode.encodeItems items).length - encodeItemsPrefixLen items n := by
    omega
  exact Nat.le_trans hle (Nat.sub_le _ _)

/-- Short-list payload bound ⇒ each item encode length ≤ 55. -/
theorem encode_item_length_le_55_of_short_list (items : List RLPItem) (n : Nat)
    (hn : n < items.length)
    (hshort : (encode.encodeItems items).length ≤ 55) :
    (encode (items[n]'hn)).length ≤ 55 :=
  Nat.le_trans (encode_item_length_le_encodeItems items n hn) hshort

/-- Cursor arithmetic helper used by packaging hnext. -/
theorem txBase_add_srcOff_add_nat (txBase : Word) (srcOff k : Nat)
    (hover : txBase.toNat + srcOff < 2 ^ 64)
    (hspan : txBase.toNat + srcOff + k < 2 ^ 64) :
    (txBase + BitVec.ofNat 64 srcOff) + BitVec.ofNat 64 k =
      txBase + BitVec.ofNat 64 (srcOff + k) := by
  apply BitVec.eq_of_toNat_eq
  have hsrc' : srcOff < 2 ^ 64 := by omega
  have hk' : k < 2 ^ 64 := by omega
  have hsk : srcOff + k < 2 ^ 64 := by omega
  have hsrc'' : (BitVec.ofNat 64 srcOff).toNat = srcOff := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsrc']
  have hk'' : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk']
  have htb : (txBase + BitVec.ofNat 64 srcOff).toNat = txBase.toNat + srcOff := by
    rw [BitVec.toNat_add, hsrc'']; omega
  have hl : ((txBase + BitVec.ofNat 64 srcOff) + BitVec.ofNat 64 k).toNat =
      txBase.toNat + srcOff + k := by
    rw [BitVec.toNat_add, htb, hk'']; omega
  have hr : (txBase + BitVec.ofNat 64 (srcOff + k)).toNat =
      txBase.toNat + (srcOff + k) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsk]; omega
  omega

/-- Single-byte field at `shortListSrcOff n` ⇒ packaging hnext to `shortListSrcOff (n+1)`. -/
theorem hnext_single_matches_srcOff_succ
    (txBytes : List (BitVec 8)) (txBase : Word) (listOff : Nat)
    (items : List RLPItem) (n : Nat) (hn : n < items.length)
    (b : Byte) (hb : b.toNat < 0x80)
    (hitem : items[n]'hn = .bytes [b])
    (henc : txBytes.drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hover : txBase.toNat + shortListSrcOff listOff items n < 2 ^ 64)
    (hspan : txBase.toNat + shortListSrcOff listOff items (n + 1) < 2 ^ 64) :
    let srcOff := shortListSrcOff listOff items n
    let srcOff' := shortListSrcOff listOff items (n + 1)
    ∀ (endPtr next len : Word),
      rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
        endPtr next len →
      next = txBase + BitVec.ofNat 64 srcOff' := by
  intro srcOff srcOff' endPtr next len hdec
  have henc1 : encode (.bytes [b]) = [b] := encode_bytes_single b hb
  have hlen1 : (encode (.bytes [b])).length = 1 := by rw [henc1]; rfl
  have hdrop := short_list_item_drop txBytes listOff items n henc hshort hn
  have hdrop' : txBytes.drop srcOff = b :: encode.encodeItems (items.drop (n + 1)) := by
    simpa [srcOff, shortListSrcOff, hitem, henc1] using hdrop
  obtain ⟨hoff, hbp⟩ := getElem_of_drop_cons txBytes srcOff b _ hdrop'
  have hover' : txBase.toNat + srcOff < 2 ^ 64 := by simpa [srcOff] using hover
  have hsucc : srcOff' = srcOff + 1 := by
    have h := shortListSrcOff_succ listOff items n hn
    simpa [srcOff, srcOff', hitem, hlen1] using h
  have hspan1 : txBase.toNat + srcOff + 1 < 2 ^ 64 := by
    have hsp : txBase.toNat + srcOff' < 2 ^ 64 := by simpa [srcOff'] using hspan
    rwa [hsucc] at hsp
  have hnext := hnext_single_byte_of_pfx txBytes txBase srcOff hoff
    (by simpa [hbp] using hb) hover' hspan1 endPtr next len hdec
  rwa [← hsucc] at hnext

/-- Creation type234 short: `srcOff5 = shortListSrcOff listOff items 5` packages hcre. -/
theorem extractSuccess_creation_type234_hcre_srcOff
    (txBytes : List (BitVec 8)) (txBase : Word)
    (h : extractSuccess txBytes)
    (hcreFlag : (teerExtractToAddress txBytes).2.2 = (1 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch txBytes).2.1.toNat)
    (items : List RLPItem)
    (hdecL : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55) :
    let listOff := (teerTxTypeDispatch txBytes).2.2.toNat
    let srcOff5 := shortListSrcOff listOff items 5
    ∀ (endPtr next5 len5 : Word),
      rlpItemDecode txBytes srcOff5 (txBase + BitVec.ofNat 64 srcOff5)
        endPtr next5 len5 → len5 = (0 : Word) := by
  intro listOff srcOff5
  exact extractSuccess_creation_type234_hcre txBytes txBase srcOff5 h hcreFlag hge
    items hdecL hshort rfl

/-- Creation type234 short field-5 empty ⇒ packaging hnext from field 5 is +1 span
    (useful when chaining past the `to` field after creation decode). -/
theorem extractSuccess_creation_type234_hnext_field5
    (txBytes : List (BitVec 8)) (txBase : Word)
    (h : extractSuccess txBytes)
    (hcreFlag : (teerExtractToAddress txBytes).2.2 = (1 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch txBytes).2.1.toNat)
    (items : List RLPItem)
    (hdecL : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hover : txBase.toNat +
        shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5 < 2 ^ 64)
    (hspan : txBase.toNat +
        shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 6 < 2 ^ 64) :
    let listOff := (teerTxTypeDispatch txBytes).2.2.toNat
    let srcOff5 := shortListSrcOff listOff items 5
    let srcOff6 := shortListSrcOff listOff items 6
    ∀ (endPtr next len : Word),
      rlpItemDecode txBytes srcOff5 (txBase + BitVec.ofNat 64 srcOff5)
        endPtr next len →
      next = txBase + BitVec.ofNat 64 srcOff6 := by
  intro listOff srcOff5 srcOff6 endPtr next len hdec
  have hf := extractSuccess_creation_type234_field5_pfx80 txBytes h hcreFlag hge
    items hdecL hshort
  have hn : (5 : Nat) < items.length := hf.1
  have hget : items[5]? = some (.bytes []) := hf.2.1
  have hitem : items[5]'hn = .bytes [] := (List.getElem?_eq_some_iff.mp hget).2
  have hencFull := decodeListItems_eq_encode _ _ hdecL
  exact hnext_empty_matches_srcOff_succ txBytes txBase listOff items 5 hn hitem
    hencFull hshort hover hspan endPtr next len hdec

#print axioms encode_item_length_le_encodeItems
#print axioms encode_item_length_le_55_of_short_list
#print axioms txBase_add_srcOff_add_nat
#print axioms hnext_single_matches_srcOff_succ
#print axioms extractSuccess_creation_type234_hcre_srcOff
#print axioms extractSuccess_creation_type234_hnext_field5

/-- Short-string encode form for `.bytes data` when not the single-byte special case.
    Covers empty, high single-byte (`b ≥ 0x80`), and multi-byte `len ≤ 55`. -/
theorem encode_bytes_short_string (data : List Byte)
    (hlen : data.length ≤ 55)
    (hnotSingle : ¬ (∃ b : Byte, data = [b] ∧ b.toNat < 0x80)) :
    encode (.bytes data) = [BitVec.ofNat 8 (0x80 + data.length)] ++ data := by
  cases data with
  | nil =>
    have h0 : (0 : Nat) ≤ 55 := by decide
    simp only [encode, encodeBytes, List.length_nil, h0, ↓reduceIte]
  | cons b tail =>
    cases tail with
    | nil =>
      by_cases hb : b.toNat < 0x80
      · exact False.elim (hnotSingle ⟨b, rfl, hb⟩)
      · -- encodeBytes [b] with b ≥ 0x80 = [0x81, b]
        simp only [encode, encodeBytes, hb, ↓reduceIte]
        have h81 : BitVec.ofNat 8 0x81 = BitVec.ofNat 8 (0x80 + 1) := by decide
        have hlen1 : [b].length = 1 := rfl
        simp only [h81, hlen1, List.cons_append, List.nil_append]
    | cons c rest =>
      have hne1 : (b :: c :: rest).length ≠ 1 := by
        intro h; cases h
      simpa [encode] using
        (encodeBytes_short_of_length_ne_one (b :: c :: rest) hlen hne1)

/-- Encode length of short-string `.bytes` (non single-byte form) is `1 + data.length`. -/
theorem encode_bytes_short_string_length (data : List Byte)
    (hlen : data.length ≤ 55)
    (hnotSingle : ¬ (∃ b : Byte, data = [b] ∧ b.toNat < 0x80)) :
    (encode (.bytes data)).length = 1 + data.length := by
  rw [encode_bytes_short_string data hlen hnotSingle]
  simp [Nat.add_comm]

/-- `Nat.toBytesBE` of a positive number is non-empty (local copy of LongItemStride). -/
private theorem toBytesBE_length_pos {n : Nat} (h : 0 < n) :
    0 < (Nat.toBytesBE n).length := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.toBytesBE_succ, List.length_append, List.length_cons, List.length_nil]
  omega

/-- Long-form `.bytes` encode (payload ≥ 56) has length > 55. -/
theorem encode_bytes_long_length_gt (data : List Byte) (hge : 56 ≤ data.length) :
    55 < (encode (.bytes data)).length := by
  cases data with
  | nil =>
    simp only [List.length_nil] at hge; omega
  | cons a tail =>
    cases tail with
    | nil =>
      simp only [List.length_cons, List.length_nil] at hge; omega
    | cons b rest =>
      have hlen_ab : (a :: b :: rest).length = rest.length + 2 := by
        simp [List.length_cons]
      have hge' : 56 ≤ rest.length + 2 := by
        simpa [hlen_ab] using hge
      have hLen : ¬ (a :: b :: rest).length ≤ 55 := by
        rw [hlen_ab]; omega
      -- force long-form branch of encodeBytes (not the singleton arm)
      simp only [encode, encodeBytes, hLen, ↓reduceIte]
      set lenBytes := Nat.toBytesBE (a :: b :: rest).length with hlb
      have hpos : 0 < lenBytes.length := by
        rw [hlb, hlen_ab]; exact toBytesBE_length_pos (by omega)
      -- encode = [pfx] ++ lenBytes ++ (a::b::rest)
      -- length = 1 + lenBytes.length + (rest.length + 2)
      change 55 <
          ([BitVec.ofNat 8 (0xB7 + lenBytes.length)] ++ lenBytes ++ (a :: b :: rest)).length
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- Under encode-length ≤ 55, a non-single-byte `.bytes` payload has `data.length ≤ 55`. -/
theorem bytes_data_length_le_55_of_encode_le
    (data : List Byte)
    (hencLe : (encode (.bytes data)).length ≤ 55)
    (_hnotSingle : ¬ (∃ b : Byte, data = [b] ∧ b.toNat < 0x80)) :
    data.length ≤ 55 := by
  by_cases hle : data.length ≤ 55
  · exact hle
  · have hge : 56 ≤ data.length := by omega
    have hgt := encode_bytes_long_length_gt data hge
    omega

/-- Short-string (non single-byte) field at `shortListSrcOff n` ⇒ packaging hnext
    to `shortListSrcOff (n+1)`. -/
theorem hnext_short_string_matches_srcOff_succ
    (txBytes : List (BitVec 8)) (txBase : Word) (listOff : Nat)
    (items : List RLPItem) (n : Nat) (hn : n < items.length)
    (data : List Byte)
    (hitem : items[n]'hn = .bytes data)
    (hlen : data.length ≤ 55)
    (hnotSingle : ¬ (∃ b : Byte, data = [b] ∧ b.toNat < 0x80))
    (henc : txBytes.drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hover : txBase.toNat + shortListSrcOff listOff items n < 2 ^ 64)
    (hspan : txBase.toNat + shortListSrcOff listOff items (n + 1) < 2 ^ 64) :
    let srcOff := shortListSrcOff listOff items n
    let srcOff' := shortListSrcOff listOff items (n + 1)
    ∀ (endPtr next len : Word),
      rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
        endPtr next len →
      next = txBase + BitVec.ofNat 64 srcOff' := by
  intro srcOff srcOff' endPtr next len hdec
  have hdrop := short_list_item_drop txBytes listOff items n henc hshort hn
  have hencI := encode_bytes_short_string data hlen hnotSingle
  have hdrop' :
      txBytes.drop srcOff =
        BitVec.ofNat 8 (0x80 + data.length) ::
          (data ++ encode.encodeItems (items.drop (n + 1))) := by
    have : encode (items[n]'hn) = [BitVec.ofNat 8 (0x80 + data.length)] ++ data := by
      rw [hitem, hencI]
    simpa [srcOff, shortListSrcOff, this, List.cons_append] using hdrop
  obtain ⟨hoff, hb⟩ :=
    getElem_of_drop_cons txBytes srcOff (BitVec.ofNat 8 (0x80 + data.length)) _ hdrop'
  have hover' : txBase.toNat + srcOff < 2 ^ 64 := by simpa [srcOff] using hover
  have hp : (BitVec.ofNat 8 (0x80 + data.length)).toNat = 0x80 + data.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hze : ((BitVec.ofNat 8 (0x80 + data.length)).zeroExtend 64).toNat =
      0x80 + data.length := by
    rw [toNat_zeroExtend_byte, hp]
  have hgePfx : ¬ BitVec.ult
      ((BitVec.ofNat 8 (0x80 + data.length)).zeroExtend 64) (0x80 : Word) = true := by
    have h80 : (0x80 : Word).toNat = 0x80 := by decide
    intro hult
    have := (BitVec.ult_iff_lt).1 hult
    simp only [BitVec.lt_def, hze, h80] at this
    omega
  have hltPfx : BitVec.ult
      ((BitVec.ofNat 8 (0x80 + data.length)).zeroExtend 64) (0xb8 : Word) = true := by
    have hb8 : (0xb8 : Word).toNat = 0xb8 := by decide
    exact (BitVec.ult_iff_lt).2 (by simp only [BitVec.lt_def, hze, hb8]; omega)
  have hge : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true := by
    rw [hb]; exact hgePfx
  have hlt : BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true := by
    rw [hb]; exact hltPfx
  have hbform : ∃ b : BitVec 8, txBytes[srcOff]? = some b ∧
      ¬ BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true ∧
      BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true :=
    ⟨txBytes[srcOff]'hoff, List.getElem?_eq_getElem hoff, hge, hlt⟩
  have hlenEq : len.toNat = data.length := by
    obtain ⟨b, hb?, hforms⟩ := hdec
    have heq : b = txBytes[srcOff]'hoff := by
      have hget : txBytes[srcOff]? = some (txBytes[srcOff]'hoff) :=
        List.getElem?_eq_getElem hoff
      rw [hget] at hb?
      exact Option.some.inj hb?.symm
    have hgeB : ¬ BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true := by
      rw [heq]; exact hge
    have hltB : BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true := by
      rw [heq]; exact hlt
    rcases hforms with h1 | h2 | h3 | h4 | h5
    · exact absurd h1.1 hgeB
    · have hlen' : len = b.zeroExtend 64 - (0x80 : Word) := h2.2.2.2.2.2
      rw [hlen', heq, hb]
      apply Eq.symm
      have h80 : (0x80 : Word).toNat = 0x80 := by decide
      have hle : 0x80 ≤ ((BitVec.ofNat 8 (0x80 + data.length)).zeroExtend 64).toNat := by
        rw [hze]; omega
      rw [BitVec.toNat_sub_of_le hle, hze, h80]
      omega
    · exact absurd hltB h3.1
    · have hb8n : (0xb8 : Word).toNat = 0xb8 := by decide
      have hc0 : (0xc0 : Word).toNat = 0xc0 := by decide
      have hltN : (b.zeroExtend 64).toNat < 0xb8 := by
        have := (BitVec.ult_iff_lt).1 hltB
        simpa [BitVec.lt_def, hb8n] using this
      have hult : BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true :=
        (BitVec.ult_iff_lt).2 (by
          have : (b.zeroExtend 64).toNat < 0xc0 := by omega
          simpa [BitVec.lt_def, hc0] using this)
      exact absurd hult h4.1
    · have hb8n : (0xb8 : Word).toNat = 0xb8 := by decide
      have hf8 : (0xf8 : Word).toNat = 0xf8 := by decide
      have hltN : (b.zeroExtend 64).toNat < 0xb8 := by
        have := (BitVec.ult_iff_lt).1 hltB
        simpa [BitVec.lt_def, hb8n] using this
      have hult : BitVec.ult (b.zeroExtend 64) (0xf8 : Word) = true :=
        (BitVec.ult_iff_lt).2 (by
          have : (b.zeroExtend 64).toNat < 0xf8 := by omega
          simpa [BitVec.lt_def, hf8] using this)
      exact absurd hult h5.1
  have hlenc : (encode (items[n]'hn)).length = 1 + data.length := by
    rw [hitem, encode_bytes_short_string_length data hlen hnotSingle]
  have hsrc' : srcOff' = srcOff + (1 + data.length) := by
    have hsucc := shortListSrcOff_succ listOff items n hn
    simpa [srcOff, srcOff', hlenc] using hsucc
  have hspan1 : txBase.toNat + srcOff + 1 + len.toNat < 2 ^ 64 := by
    have hsp : txBase.toNat + srcOff' < 2 ^ 64 := by simpa [srcOff'] using hspan
    rw [hsrc'] at hsp
    rw [hlenEq]
    omega
  have hnext := hnext_short_string_of_decode txBytes txBase srcOff endPtr next len
    hover' hdec hbform hspan1
  rw [hlenEq] at hnext
  have hadd : srcOff + 1 + data.length = srcOff + (1 + data.length) := by omega
  rw [hadd, ← hsrc'] at hnext
  exact hnext

/-- Unified packaging hnext for `.bytes` fields under short list (all short forms). -/
theorem hnext_bytes_matches_srcOff_succ
    (txBytes : List (BitVec 8)) (txBase : Word) (listOff : Nat)
    (items : List RLPItem) (n : Nat) (hn : n < items.length)
    (data : List Byte)
    (hitem : items[n]'hn = .bytes data)
    (henc : txBytes.drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hover : txBase.toNat + shortListSrcOff listOff items n < 2 ^ 64)
    (hspan : txBase.toNat + shortListSrcOff listOff items (n + 1) < 2 ^ 64) :
    let srcOff := shortListSrcOff listOff items n
    let srcOff' := shortListSrcOff listOff items (n + 1)
    ∀ (endPtr next len : Word),
      rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
        endPtr next len →
      next = txBase + BitVec.ofNat 64 srcOff' := by
  intro srcOff srcOff' endPtr next len hdec
  have hitemLen : (encode (items[n]'hn)).length ≤ 55 :=
    encode_item_length_le_55_of_short_list items n hn hshort
  have hdataLen : (encode (.bytes data)).length ≤ 55 := by
    simpa [hitem] using hitemLen
  by_cases hsingle : ∃ b : Byte, data = [b] ∧ b.toNat < 0x80
  · obtain ⟨b, hdata, hb⟩ := hsingle
    subst hdata
    exact hnext_single_matches_srcOff_succ txBytes txBase listOff items n hn b hb
      hitem henc hshort hover hspan endPtr next len hdec
  · have hlenD := bytes_data_length_le_55_of_encode_le data hdataLen hsingle
    exact hnext_short_string_matches_srcOff_succ txBytes txBase listOff items n hn
      data hitem hlenD hsingle henc hshort hover hspan endPtr next len hdec

#print axioms encode_bytes_short_string
#print axioms encode_bytes_short_string_length
#print axioms bytes_data_length_le_55_of_encode_le
#print axioms hnext_short_string_matches_srcOff_succ
#print axioms hnext_bytes_matches_srcOff_succ

/-- Long-list encode (payload > 55) has total length > 55. -/
theorem encode_list_long_length_gt (items : List RLPItem)
    (hge : 55 < (encode.encodeItems items).length) :
    55 < (encode (.list items)).length := by
  rw [encode_list_long items hge]
  simp only [List.length_cons, List.length_append]
  have hpos : 0 < (Nat.toBytesBE (encode.encodeItems items).length).length :=
    toBytesBE_length_pos (by omega)
  omega

/-- Under encode-length ≤ 55, a `.list` item uses short-list form with payload ≤ 55. -/
theorem encode_list_of_encode_le_55 (sub : List RLPItem)
    (hle : (encode (.list sub)).length ≤ 55) :
    (encode.encodeItems sub).length ≤ 55 ∧
      encode (.list sub) =
        BitVec.ofNat 8 (0xC0 + (encode.encodeItems sub).length)
          :: encode.encodeItems sub := by
  by_cases hp : (encode.encodeItems sub).length ≤ 55
  · exact ⟨hp, encode_list_short sub hp⟩
  · have hgt : 55 < (encode.encodeItems sub).length := by omega
    have := encode_list_long_length_gt sub hgt
    omega

/-- Short-list nested field at `shortListSrcOff n` ⇒ packaging hnext to succ. -/
theorem hnext_short_list_matches_srcOff_succ
    (txBytes : List (BitVec 8)) (txBase : Word) (listOff : Nat)
    (items : List RLPItem) (n : Nat) (hn : n < items.length)
    (sub : List RLPItem)
    (hitem : items[n]'hn = .list sub)
    (henc : txBytes.drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hover : txBase.toNat + shortListSrcOff listOff items n < 2 ^ 64)
    (hspan : txBase.toNat + shortListSrcOff listOff items (n + 1) < 2 ^ 64) :
    let srcOff := shortListSrcOff listOff items n
    let srcOff' := shortListSrcOff listOff items (n + 1)
    ∀ (endPtr next len : Word),
      rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
        endPtr next len →
      next = txBase + BitVec.ofNat 64 srcOff' := by
  intro srcOff srcOff' endPtr next len hdec
  have hitemLen : (encode (items[n]'hn)).length ≤ 55 :=
    encode_item_length_le_55_of_short_list items n hn hshort
  have hencLen : (encode (.list sub)).length ≤ 55 := by simpa [hitem] using hitemLen
  obtain ⟨hpayLe, hencForm⟩ := encode_list_of_encode_le_55 sub hencLen
  set pay := (encode.encodeItems sub).length with hpay_def
  have hpayLe' : pay ≤ 55 := by simpa [hpay_def] using hpayLe
  have hdrop := short_list_item_drop txBytes listOff items n henc hshort hn
  have hdrop' :
      txBytes.drop srcOff =
        BitVec.ofNat 8 (0xC0 + pay) ::
          (encode.encodeItems sub ++ encode.encodeItems (items.drop (n + 1))) := by
    have : encode (items[n]'hn) =
        BitVec.ofNat 8 (0xC0 + pay) :: encode.encodeItems sub := by
      rw [hitem, hencForm, hpay_def]
    simpa [srcOff, shortListSrcOff, this, List.cons_append] using hdrop
  obtain ⟨hoff, hb⟩ :=
    getElem_of_drop_cons txBytes srcOff (BitVec.ofNat 8 (0xC0 + pay)) _ hdrop'
  have hover' : txBase.toNat + srcOff < 2 ^ 64 := by simpa [srcOff] using hover
  have hp : (BitVec.ofNat 8 (0xC0 + pay)).toNat = 0xC0 + pay := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hzePfx : ((BitVec.ofNat 8 (0xC0 + pay)).zeroExtend 64).toNat = 0xC0 + pay := by
    rw [toNat_zeroExtend_byte, hp]
  have hge80 : ¬ BitVec.ult
      ((txBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true := by
    rw [hb]
    have h80 : (0x80 : Word).toNat = 0x80 := by decide
    intro hult
    have := (BitVec.ult_iff_lt).1 hult
    simp only [BitVec.lt_def, hzePfx, h80] at this; omega
  have hgeC0 : ¬ BitVec.ult
      ((txBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true := by
    rw [hb]
    have hc0 : (0xc0 : Word).toNat = 0xc0 := by decide
    intro hult
    have := (BitVec.ult_iff_lt).1 hult
    simp only [BitVec.lt_def, hzePfx, hc0] at this; omega
  have hltF8 : BitVec.ult
      ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true := by
    rw [hb]
    have hf8 : (0xf8 : Word).toNat = 0xf8 := by decide
    exact (BitVec.ult_iff_lt).2 (by simp only [BitVec.lt_def, hzePfx, hf8]; omega)
  have hlenc : (encode (items[n]'hn)).length = 1 + pay := by
    rw [hitem, hencForm]
    -- encode = pfx :: payload, |payload| = pay
    simp [List.length_cons, ← hpay_def, Nat.add_comm]
  have hsrc' : srcOff' = srcOff + (1 + pay) := by
    have hsucc := shortListSrcOff_succ listOff items n hn
    simpa [srcOff, srcOff', hlenc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hsucc
  obtain ⟨b, hb?, hforms⟩ := hdec
  have heq : b = txBytes[srcOff]'hoff := by
    have hget : txBytes[srcOff]? = some (txBytes[srcOff]'hoff) :=
      List.getElem?_eq_getElem hoff
    rw [hget] at hb?
    exact Option.some.inj hb?.symm
  have hge80b : ¬ BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true := by
    rw [heq]; exact hge80
  have hgeC0b : ¬ BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true := by
    rw [heq]; exact hgeC0
  have hltF8b : BitVec.ult (b.zeroExtend 64) (0xf8 : Word) = true := by
    rw [heq]; exact hltF8
  have hbEq : b = BitVec.ofNat 8 (0xC0 + pay) := by rw [heq, hb]
  have hzeB : (b.zeroExtend 64).toNat = 0xC0 + pay := by
    rw [toNat_zeroExtend_byte, hbEq, hp]
  rcases hforms with h1 | h2 | h3 | h4 | h5
  · exact absurd h1.1 hge80b
  · -- short string requires p < 0xb8, but p ≥ 0xc0
    have hb8 : (0xb8 : Word).toNat = 0xb8 := by decide
    have hltN : ¬ BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true := by
      intro hult
      have := (BitVec.ult_iff_lt).1 hult
      simp only [BitVec.lt_def, hzeB, hb8] at this; omega
    exact absurd h2.2.1 hltN
  · -- long string requires p < 0xc0
    exact absurd h3.2.1 hgeC0b
  · -- short list arm
    have hnextEq :
        next = (txBase + BitVec.ofNat 64 srcOff) +
          ((b.zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)) :=
      h4.2.2.2.1
    have hse1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    have hc0 : (0xc0 : Word).toNat = 0xc0 := by decide
    have hsub : b.zeroExtend 64 - (0xc0 : Word) = BitVec.ofNat 64 pay := by
      apply BitVec.eq_of_toNat_eq
      have hle : 0xc0 ≤ (b.zeroExtend 64).toNat := by omega
      rw [BitVec.toNat_sub_of_le hle, hzeB, hc0, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
      omega
    have h1 : ((1 : Word).toNat) = 1 := by decide
    have hsrcN : (BitVec.ofNat 64 srcOff).toNat = srcOff := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpayW : (BitVec.ofNat 64 pay).toNat = pay := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hcursor : (txBase + BitVec.ofNat 64 srcOff).toNat = txBase.toNat + srcOff := by
      rw [BitVec.toNat_add, hsrcN]; omega
    have hspanN : txBase.toNat + srcOff + pay + 1 < 2 ^ 64 := by
      have hsp : txBase.toNat + srcOff' < 2 ^ 64 := by simpa [srcOff'] using hspan
      rw [hsrc'] at hsp; omega
    have hnextN : next.toNat = txBase.toNat + srcOff + pay + 1 := by
      rw [hnextEq, hse1, hsub]
      -- next = cursor + (payW + 1)
      have hsum :
          ((txBase + BitVec.ofNat 64 srcOff) +
            (BitVec.ofNat 64 pay + (1 : Word))).toNat =
            txBase.toNat + srcOff + pay + 1 := by
        have hmid :
            ((txBase + BitVec.ofNat 64 srcOff) + BitVec.ofNat 64 pay).toNat =
              txBase.toNat + srcOff + pay := by
          rw [BitVec.toNat_add, hcursor, hpayW]; omega
        -- (cursor + pay) + 1
        have hre : (txBase + BitVec.ofNat 64 srcOff) +
            (BitVec.ofNat 64 pay + (1 : Word)) =
            ((txBase + BitVec.ofNat 64 srcOff) + BitVec.ofNat 64 pay) + (1 : Word) := by
          ac_rfl
        rw [hre, BitVec.toNat_add, hmid, h1]; omega
      exact hsum
    apply BitVec.eq_of_toNat_eq
    have hr : (txBase + BitVec.ofNat 64 srcOff').toNat = txBase.toNat + srcOff' := by
      have hoff' : srcOff' < 2 ^ 64 := by omega
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff']; omega
    rw [hnextN, hr, hsrc']; omega
  · exact absurd hltF8b h5.1

/-- Unified packaging hnext for any short-list field (bytes or nested list). -/
theorem hnext_item_matches_srcOff_succ
    (txBytes : List (BitVec 8)) (txBase : Word) (listOff : Nat)
    (items : List RLPItem) (n : Nat) (hn : n < items.length)
    (henc : txBytes.drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hover : txBase.toNat + shortListSrcOff listOff items n < 2 ^ 64)
    (hspan : txBase.toNat + shortListSrcOff listOff items (n + 1) < 2 ^ 64) :
    let srcOff := shortListSrcOff listOff items n
    let srcOff' := shortListSrcOff listOff items (n + 1)
    ∀ (endPtr next len : Word),
      rlpItemDecode txBytes srcOff (txBase + BitVec.ofNat 64 srcOff)
        endPtr next len →
      next = txBase + BitVec.ofNat 64 srcOff' := by
  intro srcOff srcOff' endPtr next len hdec
  match hitem : items[n]'hn with
  | .bytes data =>
    exact hnext_bytes_matches_srcOff_succ txBytes txBase listOff items n hn data
      hitem henc hshort hover hspan endPtr next len hdec
  | .list sub =>
    exact hnext_short_list_matches_srcOff_succ txBytes txBase listOff items n hn sub
      hitem henc hshort hover hspan endPtr next len hdec

#print axioms encode_list_long_length_gt
#print axioms encode_list_of_encode_le_55
#print axioms hnext_short_list_matches_srcOff_succ
#print axioms hnext_item_matches_srcOff_succ

/-- Packaging form: decode-gated hnext at `shortListSrcOff k` → `shortListSrcOff (k+1)`. -/
theorem packaging_hnext_shortListSrcOff
    (txBytes : List (BitVec 8)) (txBase : Word) (listOff : Nat)
    (items : List RLPItem) (k : Nat) (hk : k < items.length)
    (henc : txBytes.drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hover : txBase.toNat + shortListSrcOff listOff items k < 2 ^ 64)
    (hspan : txBase.toNat + shortListSrcOff listOff items (k + 1) < 2 ^ 64) :
    ∀ (endPtr next len : Word),
      rlpItemDecode txBytes (shortListSrcOff listOff items k)
        (txBase + BitVec.ofNat 64 (shortListSrcOff listOff items k))
        endPtr next len →
      next = txBase + BitVec.ofNat 64 (shortListSrcOff listOff items (k + 1)) := by
  intro endPtr next len hdec
  exact hnext_item_matches_srcOff_succ txBytes txBase listOff items k hk
    henc hshort hover hspan endPtr next len hdec

/-- Creation type234 short: items has length ≥ 6 (field5 exists). -/
theorem extractSuccess_creation_type234_items_length
    (txBytes : List (BitVec 8))
    (h : extractSuccess txBytes)
    (hcreFlag : (teerExtractToAddress txBytes).2.2 = (1 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch txBytes).2.1.toNat)
    (items : List RLPItem)
    (hdecL : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55) :
    6 ≤ items.length := by
  have hf := extractSuccess_creation_type234_field5_pfx80 txBytes h hcreFlag hge
    items hdecL hshort
  omega

/-- Creation type234 short: discharge packaging hnext1..5 + hcre with
    `srcOff k = shortListSrcOff listOff items k`. -/
theorem extractSuccess_creation_type234_hnext_hcre_srcOff
    (txBytes : List (BitVec 8)) (txBase : Word)
    (h : extractSuccess txBytes)
    (hcreFlag : (teerExtractToAddress txBytes).2.2 = (1 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch txBytes).2.1.toNat)
    (items : List RLPItem)
    (hdecL : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hover0 : txBase.toNat +
        shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 0 < 2 ^ 64)
    (hover1 : txBase.toNat +
        shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 1 < 2 ^ 64)
    (hover2 : txBase.toNat +
        shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 2 < 2 ^ 64)
    (hover3 : txBase.toNat +
        shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 3 < 2 ^ 64)
    (hover4 : txBase.toNat +
        shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 4 < 2 ^ 64)
    (hover5 : txBase.toNat +
        shortListSrcOff (teerTxTypeDispatch txBytes).2.2.toNat items 5 < 2 ^ 64) :
    let listOff := (teerTxTypeDispatch txBytes).2.2.toNat
    let srcOff0 := shortListSrcOff listOff items 0
    let srcOff1 := shortListSrcOff listOff items 1
    let srcOff2 := shortListSrcOff listOff items 2
    let srcOff3 := shortListSrcOff listOff items 3
    let srcOff4 := shortListSrcOff listOff items 4
    let srcOff5 := shortListSrcOff listOff items 5
    (∀ (endPtr next0 len0 : Word),
      rlpItemDecode txBytes srcOff0 (txBase + BitVec.ofNat 64 srcOff0)
        endPtr next0 len0 →
      next0 = txBase + BitVec.ofNat 64 srcOff1) ∧
    (∀ (endPtr next1 len1 : Word),
      rlpItemDecode txBytes srcOff1 (txBase + BitVec.ofNat 64 srcOff1)
        endPtr next1 len1 →
      next1 = txBase + BitVec.ofNat 64 srcOff2) ∧
    (∀ (endPtr next2 len2 : Word),
      rlpItemDecode txBytes srcOff2 (txBase + BitVec.ofNat 64 srcOff2)
        endPtr next2 len2 →
      next2 = txBase + BitVec.ofNat 64 srcOff3) ∧
    (∀ (endPtr next3 len3 : Word),
      rlpItemDecode txBytes srcOff3 (txBase + BitVec.ofNat 64 srcOff3)
        endPtr next3 len3 →
      next3 = txBase + BitVec.ofNat 64 srcOff4) ∧
    (∀ (endPtr next4 len4 : Word),
      rlpItemDecode txBytes srcOff4 (txBase + BitVec.ofNat 64 srcOff4)
        endPtr next4 len4 →
      next4 = txBase + BitVec.ofNat 64 srcOff5) ∧
    (∀ (endPtr next5 len5 : Word),
      rlpItemDecode txBytes srcOff5 (txBase + BitVec.ofNat 64 srcOff5)
        endPtr next5 len5 → len5 = (0 : Word)) := by
  intro listOff srcOff0 srcOff1 srcOff2 srcOff3 srcOff4 srcOff5
  have hlen := extractSuccess_creation_type234_items_length txBytes h hcreFlag hge
    items hdecL hshort
  have hn0 : (0 : Nat) < items.length := by omega
  have hn1 : (1 : Nat) < items.length := by omega
  have hn2 : (2 : Nat) < items.length := by omega
  have hn3 : (3 : Nat) < items.length := by omega
  have hn4 : (4 : Nat) < items.length := by omega
  have hn5 : (5 : Nat) < items.length := by omega
  have hencFull := decodeListItems_eq_encode _ _ hdecL
  refine ⟨?h1, ?h2, ?h3, ?h4, ?h5, ?hcre⟩
  · intro endPtr next len hdec
    exact packaging_hnext_shortListSrcOff txBytes txBase listOff items 0 hn0
      hencFull hshort hover0 hover1 endPtr next len hdec
  · intro endPtr next len hdec
    exact packaging_hnext_shortListSrcOff txBytes txBase listOff items 1 hn1
      hencFull hshort hover1 hover2 endPtr next len hdec
  · intro endPtr next len hdec
    exact packaging_hnext_shortListSrcOff txBytes txBase listOff items 2 hn2
      hencFull hshort hover2 hover3 endPtr next len hdec
  · intro endPtr next len hdec
    exact packaging_hnext_shortListSrcOff txBytes txBase listOff items 3 hn3
      hencFull hshort hover3 hover4 endPtr next len hdec
  · intro endPtr next len hdec
    exact packaging_hnext_shortListSrcOff txBytes txBase listOff items 4 hn4
      hencFull hshort hover4 hover5 endPtr next len hdec
  · -- hcre at field5; packaging endPtr quantifier matches Assumed
    intro endPtr next5 len5 hdec
    exact extractSuccess_creation_type234_hcre_srcOff txBytes txBase h hcreFlag hge
      items hdecL hshort endPtr next5 len5 hdec

#print axioms packaging_hnext_shortListSrcOff
#print axioms extractSuccess_creation_type234_items_length
#print axioms extractSuccess_creation_type234_hnext_hcre_srcOff

/-- Item encode is non-empty (every RLP item has ≥1 header byte). -/
theorem encode_item_length_pos (item : RLPItem) : 0 < (encode item).length :=
  encode_nonempty item

/-- Absolute offset of item `n` in a short list is in-bounds. -/
theorem shortListSrcOff_lt_length
    (bs : List Byte) (listOff : Nat) (items : List RLPItem) (n : Nat)
    (henc : bs.drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : n < items.length) :
    shortListSrcOff listOff items n < bs.length := by
  have hdrop := short_list_item_drop bs listOff items n henc hshort hn
  have hpos : 0 < (encode (items[n]'hn)).length := encode_item_length_pos _
  have hne : encode (items[n]'hn) ≠ [] := List.ne_nil_of_length_pos hpos
  have hcons : ∃ b rest, encode (items[n]'hn) = b :: rest := by
    match h : encode (items[n]'hn) with
    | [] => exact absurd h hne
    | b :: rest => exact ⟨b, rest, rfl⟩
  obtain ⟨b, rest, heq⟩ := hcons
  have hdrop' :
      bs.drop (shortListSrcOff listOff items n) =
        b :: (rest ++ encode.encodeItems (items.drop (n + 1))) := by
    simpa [shortListSrcOff, heq, List.cons_append] using hdrop
  obtain ⟨hoff, _⟩ := getElem_of_drop_cons bs (shortListSrcOff listOff items n) b _ hdrop'
  exact hoff

/-- `txBase + srcOff < 2^64` from buffer span and in-bounds offset. -/
theorem hover_of_buffer_span (txBase : Word) (srcOff len : Nat)
    (hover : txBase.toNat + len < 2 ^ 64)
    (hoff : srcOff < len) :
    txBase.toNat + srcOff < 2 ^ 64 := by omega

/-- Creation type234 short: hoff0..5 under `shortListSrcOff`. -/
theorem extractSuccess_creation_type234_hoff_srcOff
    (txBytes : List (BitVec 8))
    (h : extractSuccess txBytes)
    (hcreFlag : (teerExtractToAddress txBytes).2.2 = (1 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch txBytes).2.1.toNat)
    (items : List RLPItem)
    (hdecL : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55) :
    let listOff := (teerTxTypeDispatch txBytes).2.2.toNat
    shortListSrcOff listOff items 0 < txBytes.length ∧
    shortListSrcOff listOff items 1 < txBytes.length ∧
    shortListSrcOff listOff items 2 < txBytes.length ∧
    shortListSrcOff listOff items 3 < txBytes.length ∧
    shortListSrcOff listOff items 4 < txBytes.length ∧
    shortListSrcOff listOff items 5 < txBytes.length := by
  intro listOff
  have hlen := extractSuccess_creation_type234_items_length txBytes h hcreFlag hge
    items hdecL hshort
  have henc := decodeListItems_eq_encode _ _ hdecL
  have hn0 : (0 : Nat) < items.length := by omega
  have hn1 : (1 : Nat) < items.length := by omega
  have hn2 : (2 : Nat) < items.length := by omega
  have hn3 : (3 : Nat) < items.length := by omega
  have hn4 : (4 : Nat) < items.length := by omega
  have hn5 : (5 : Nat) < items.length := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact shortListSrcOff_lt_length txBytes listOff items 0 henc hshort hn0
  · exact shortListSrcOff_lt_length txBytes listOff items 1 henc hshort hn1
  · exact shortListSrcOff_lt_length txBytes listOff items 2 henc hshort hn2
  · exact shortListSrcOff_lt_length txBytes listOff items 3 henc hshort hn3
  · exact shortListSrcOff_lt_length txBytes listOff items 4 henc hshort hn4
  · exact shortListSrcOff_lt_length txBytes listOff items 5 henc hshort hn5

/-- Creation type234 short: hover0..5 from buffer span + hoff. -/
theorem extractSuccess_creation_type234_hover_srcOff
    (txBytes : List (BitVec 8)) (txBase : Word)
    (h : extractSuccess txBytes)
    (hcreFlag : (teerExtractToAddress txBytes).2.2 = (1 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch txBytes).2.1.toNat)
    (items : List RLPItem)
    (hdecL : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64) :
    let listOff := (teerTxTypeDispatch txBytes).2.2.toNat
    txBase.toNat + shortListSrcOff listOff items 0 < 2 ^ 64 ∧
    txBase.toNat + shortListSrcOff listOff items 1 < 2 ^ 64 ∧
    txBase.toNat + shortListSrcOff listOff items 2 < 2 ^ 64 ∧
    txBase.toNat + shortListSrcOff listOff items 3 < 2 ^ 64 ∧
    txBase.toNat + shortListSrcOff listOff items 4 < 2 ^ 64 ∧
    txBase.toNat + shortListSrcOff listOff items 5 < 2 ^ 64 := by
  intro listOff
  have hoffs := extractSuccess_creation_type234_hoff_srcOff txBytes h hcreFlag hge
    items hdecL hshort
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hoffs
  exact ⟨hover_of_buffer_span txBase _ _ hover h0,
    hover_of_buffer_span txBase _ _ hover h1,
    hover_of_buffer_span txBase _ _ hover h2,
    hover_of_buffer_span txBase _ _ hover h3,
    hover_of_buffer_span txBase _ _ hover h4,
    hover_of_buffer_span txBase _ _ hover h5⟩

/-- Buffer byte at short-list item offset equals encode head. -/
theorem short_list_item_head_eq
    (txBytes : List (BitVec 8)) (listOff : Nat) (items : List RLPItem) (n : Nat)
    (henc : txBytes.drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : n < items.length)
    (hoff : shortListSrcOff listOff items n < txBytes.length) :
    txBytes[shortListSrcOff listOff items n]'hoff =
      (encode (items[n]'hn))[0]'(encode_item_length_pos _) := by
  set srcOff := shortListSrcOff listOff items n
  have hdrop := short_list_item_drop txBytes listOff items n henc hshort hn
  have hpos : 0 < (encode (items[n]'hn)).length := encode_item_length_pos _
  have hcons : ∃ b rest, encode (items[n]'hn) = b :: rest := by
    match h : encode (items[n]'hn) with
    | [] => exact absurd h (List.ne_nil_of_length_pos hpos)
    | b :: rest => exact ⟨b, rest, rfl⟩
  obtain ⟨b, rest, heq⟩ := hcons
  have hdrop' :
      txBytes.drop srcOff =
        b :: (rest ++ encode.encodeItems (items.drop (n + 1))) := by
    simpa [srcOff, shortListSrcOff, heq] using hdrop
  obtain ⟨_, hb'⟩ := getElem_of_drop_cons txBytes srcOff b _ hdrop'
  simpa [heq] using hb'

/-- If item encode length ≥ 2 then short-string content offset is in-bounds. -/
theorem hss_room_of_encode_ge_two
    (txBytes : List (BitVec 8)) (listOff : Nat) (items : List RLPItem) (n : Nat)
    (henc : txBytes.drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : n < items.length)
    (hge2 : 2 ≤ (encode (items[n]'hn)).length) :
    let srcOff := shortListSrcOff listOff items n
    srcOff + 1 < txBytes.length := by
  intro srcOff
  have hdrop := short_list_item_drop txBytes listOff items n henc hshort hn
  have hlen_drop :
      (txBytes.drop srcOff).length =
        (encode (items[n]'hn)).length +
          (encode.encodeItems (items.drop (n + 1))).length := by
    have := congrArg List.length hdrop
    simpa [srcOff, shortListSrcOff, List.length_append] using this
  have hdl : (txBytes.drop srcOff).length = txBytes.length - srcOff := by
    simp [List.length_drop]
  have hsrc : srcOff < txBytes.length :=
    shortListSrcOff_lt_length txBytes listOff items n henc hshort hn
  omega

/-- Empty item that is not last: offset+1 starts the next item (in-bounds). -/
theorem hss_room_of_empty_not_last
    (txBytes : List (BitVec 8)) (listOff : Nat) (items : List RLPItem) (n : Nat)
    (henc : txBytes.drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : n < items.length)
    (hnext : n + 1 < items.length)
    (hitem : items[n]'hn = .bytes []) :
    let srcOff := shortListSrcOff listOff items n
    srcOff + 1 < txBytes.length := by
  intro srcOff
  have hencI : encode (items[n]'hn) = [BitVec.ofNat 8 0x80] := by
    rw [hitem, encode_bytes_empty]
  have hsucc :
      shortListSrcOff listOff items (n + 1) = srcOff + 1 := by
    simp only [shortListSrcOff, srcOff]
    have hpre :
        encodeItemsPrefixLen items (n + 1) =
          encodeItemsPrefixLen items n + (encode (items[n]'hn)).length :=
      encodeItemsPrefixLen_succ items n hn
    simp only [hencI, List.length_cons, List.length_nil] at hpre
    omega
  have hlt :=
    shortListSrcOff_lt_length txBytes listOff items (n + 1) henc hshort hnext
  omega

/-- Head byte of a non-empty encode list. -/
private theorem encode_head_of_cons {item : RLPItem} {b : Byte} {rest : List Byte}
    (h : encode item = b :: rest) :
    (encode item)[0]'(encode_item_length_pos item) = b := by
  simp only [h, List.getElem_cons_zero]

/-- Nat head of encode under length ≤ 55: either `< 0xb8` or in `[0xc0,0xf7]`. -/
theorem encode_item_head_toNat_bounds (item : RLPItem)
    (hle : (encode item).length ≤ 55) :
    ((encode item)[0]'(encode_item_length_pos item)).toNat < 0xb8 ∨
      (0xc0 ≤ ((encode item)[0]'(encode_item_length_pos item)).toNat ∧
        ((encode item)[0]'(encode_item_length_pos item)).toNat < 0xf8) := by
  cases item with
  | bytes data =>
    cases data with
    | nil =>
      have henc' : encode (.bytes []) = [BitVec.ofNat 8 0x80] := encode_bytes_empty
      have hb' :
          (encode (.bytes []))[0]'(encode_item_length_pos _) = BitVec.ofNat 8 0x80 :=
        encode_head_of_cons henc'
      left
      have : ((encode (.bytes []))[0]'(encode_item_length_pos _)).toNat = 0x80 := by
        rw [hb', BitVec.toNat_ofNat]
      omega
    | cons a tail =>
      cases tail with
      | nil =>
        by_cases ha : a.toNat < 0x80
        · have henc' : encode (.bytes [a]) = [a] := by
            simp only [encode, encodeBytes, ha, ↓reduceIte]
          have hb' : (encode (.bytes [a]))[0]'(encode_item_length_pos _) = a :=
            encode_head_of_cons henc'
          left
          have : ((encode (.bytes [a]))[0]'(encode_item_length_pos _)).toNat = a.toNat := by
            rw [hb']
          omega
        · have henc' : encode (.bytes [a]) = [BitVec.ofNat 8 0x81, a] := by
            simp only [encode, encodeBytes, ha, ↓reduceIte]
          have hb' :
              (encode (.bytes [a]))[0]'(encode_item_length_pos _) =
                BitVec.ofNat 8 0x81 :=
            encode_head_of_cons henc'
          left
          have : ((encode (.bytes [a]))[0]'(encode_item_length_pos _)).toNat = 0x81 := by
            rw [hb', BitVec.toNat_ofNat]
          omega
      | cons c rest =>
        by_cases hle55 : (a :: c :: rest).length ≤ 55
        · have hne1 : (a :: c :: rest).length ≠ 1 := by intro h; cases h
          have henc' :
              encode (.bytes (a :: c :: rest)) =
                BitVec.ofNat 8 (0x80 + (a :: c :: rest).length) :: (a :: c :: rest) := by
            simpa [encode, List.cons_append] using
              encodeBytes_short_of_length_ne_one (a :: c :: rest) hle55 hne1
          have hb' :
              (encode (.bytes (a :: c :: rest)))[0]'(encode_item_length_pos _) =
                BitVec.ofNat 8 (0x80 + (a :: c :: rest).length) :=
            encode_head_of_cons henc'
          left
          have :
              ((encode (.bytes (a :: c :: rest)))[0]'(encode_item_length_pos _)).toNat =
                0x80 + (a :: c :: rest).length := by
            rw [hb', BitVec.toNat_ofNat]
            exact Nat.mod_eq_of_lt (by omega)
          omega
        · have hge56 : 56 ≤ (a :: c :: rest).length := by omega
          have hgt := encode_bytes_long_length_gt (a :: c :: rest) hge56
          omega
  | list sub =>
    by_cases hp : (encode.encodeItems sub).length ≤ 55
    · have henc' := encode_list_short sub hp
      have hb' :
          (encode (.list sub))[0]'(encode_item_length_pos _) =
            BitVec.ofNat 8 (0xC0 + (encode.encodeItems sub).length) :=
        encode_head_of_cons henc'
      right
      have :
          ((encode (.list sub))[0]'(encode_item_length_pos _)).toNat =
            0xC0 + (encode.encodeItems sub).length := by
        rw [hb', BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by omega)
      omega
    · have hgt : 55 < (encode.encodeItems sub).length := by omega
      have := encode_list_long_length_gt sub hgt
      omega

/-- Under encode-length ≤ 55, item head is never a long-string prefix in `[0xb8,0xbf]`. -/
theorem encode_item_head_not_long_string (item : RLPItem)
    (hle : (encode item).length ≤ 55) :
    ¬ (¬ BitVec.ult (((encode item)[0]'(encode_item_length_pos item)).zeroExtend 64)
          (0xb8 : Word) = true ∧
        BitVec.ult (((encode item)[0]'(encode_item_length_pos item)).zeroExtend 64)
          (0xc0 : Word) = true) := by
  intro ⟨hgeB8, hltC0⟩
  set head := (encode item)[0]'(encode_item_length_pos item)
  have hb8 : (0xb8 : Word).toNat = 0xb8 := by decide
  have hc0 : (0xc0 : Word).toNat = 0xc0 := by decide
  have hze : (head.zeroExtend 64).toNat = head.toNat := toNat_zeroExtend_byte head
  have hgeN : 0xb8 ≤ head.toNat := by
    by_contra hlt
    have hlt' : head.toNat < 0xb8 := Nat.lt_of_not_ge hlt
    have hult : BitVec.ult (head.zeroExtend 64) (0xb8 : Word) = true := by
      apply (BitVec.ult_iff_lt).2
      change (head.zeroExtend 64).toNat < (0xb8 : Word).toNat
      rw [hze, hb8]; exact hlt'
    exact hgeB8 hult
  have hltN : head.toNat < 0xc0 := by
    have hult := (BitVec.ult_iff_lt).1 hltC0
    change (head.zeroExtend 64).toNat < (0xc0 : Word).toNat at hult
    rwa [hze, hc0] at hult
  have hbounds := encode_item_head_toNat_bounds item hle
  -- hbounds uses the same getElem head
  change head.toNat < 0xb8 ∨ (0xc0 ≤ head.toNat ∧ head.toNat < 0xf8) at hbounds
  rcases hbounds with hltB8 | ⟨hgeC0, _⟩
  · omega
  · omega

/-- Under encode-length ≤ 55, item head is always `< 0xf8` (never long-list). -/
theorem encode_item_head_lt_f8 (item : RLPItem)
    (hle : (encode item).length ≤ 55) :
    BitVec.ult (((encode item)[0]'(encode_item_length_pos item)).zeroExtend 64)
      (0xf8 : Word) = true := by
  set head := (encode item)[0]'(encode_item_length_pos item)
  have hf8 : (0xf8 : Word).toNat = 0xf8 := by decide
  have hze : (head.zeroExtend 64).toNat = head.toNat := toNat_zeroExtend_byte head
  have hbt : head.toNat < 0xf8 := by
    have hbounds := encode_item_head_toNat_bounds item hle
    change head.toNat < 0xb8 ∨ (0xc0 ≤ head.toNat ∧ head.toNat < 0xf8) at hbounds
    rcases hbounds with h | ⟨_, hlt⟩
    · omega
    · exact hlt
  apply (BitVec.ult_iff_lt).2
  change (head.zeroExtend 64).toNat < (0xf8 : Word).toNat
  rwa [hze, hf8]

/-- Packaging `hls`: long-string fit hyp is vacuous under short outer list. -/
theorem hls_vacuous_of_short_list_item
    (txBytes : List (BitVec 8)) (listOff : Nat) (items : List RLPItem) (n : Nat)
    (henc : txBytes.drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : n < items.length)
    (hoff : shortListSrcOff listOff items n < txBytes.length)
    {P : Prop} :
    ¬ BitVec.ult ((txBytes[shortListSrcOff listOff items n]'hoff).zeroExtend 64)
        (0xb8 : Word) = true →
      BitVec.ult ((txBytes[shortListSrcOff listOff items n]'hoff).zeroExtend 64)
        (0xc0 : Word) = true →
      P := by
  intro hgeB8 hltC0
  have hhead := short_list_item_head_eq txBytes listOff items n henc hshort hn hoff
  have hle : (encode (items[n]'hn)).length ≤ 55 :=
    encode_item_length_le_55_of_short_list items n hn hshort
  have hnot := encode_item_head_not_long_string (items[n]'hn) hle
  refine False.elim (hnot ⟨?_, ?_⟩)
  · simpa [hhead] using hgeB8
  · simpa [hhead] using hltC0

/-- Packaging `hll`: long-list fit hyp is vacuous under short outer list. -/
theorem hll_vacuous_of_short_list_item
    (txBytes : List (BitVec 8)) (listOff : Nat) (items : List RLPItem) (n : Nat)
    (henc : txBytes.drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : n < items.length)
    (hoff : shortListSrcOff listOff items n < txBytes.length)
    {P : Prop} :
    ¬ BitVec.ult ((txBytes[shortListSrcOff listOff items n]'hoff).zeroExtend 64)
        (0xf8 : Word) = true →
      P := by
  intro hgeF8
  have hhead := short_list_item_head_eq txBytes listOff items n henc hshort hn hoff
  have hle : (encode (items[n]'hn)).length ≤ 55 :=
    encode_item_length_le_55_of_short_list items n hn hshort
  have hlt := encode_item_head_lt_f8 (items[n]'hn) hle
  have hlt' :
      BitVec.ult ((txBytes[shortListSrcOff listOff items n]'hoff).zeroExtend 64)
        (0xf8 : Word) = true := by
    simpa [hhead] using hlt
  exact absurd hlt' hgeF8

/-- Length-1 encode with head in `[0x80,0xb8)` is empty bytes `0x80`. -/
theorem encode_len1_short_string_is_empty (item : RLPItem)
    (hlen1 : (encode item).length = 1)
    (hge : 0x80 ≤ ((encode item)[0]'(by rw [hlen1]; omega)).toNat)
    (hlt : ((encode item)[0]'(by rw [hlen1]; omega)).toNat < 0xb8) :
    item = .bytes [] := by
  have hle : (encode item).length ≤ 55 := by omega
  cases item with
  | list sub =>
    have hb := encode_item_head_toNat_bounds (.list sub) hle
    rcases hb with hltB8 | ⟨hgeC0, _⟩
    · -- short-list head is ≥ 0xc0, so not < 0xb8
      have henc' := encode_list_short sub (by
        have : (encode (.list sub)).length = 1 := hlen1
        -- short form length = 1 + payload; payload 0 ⇒ length 1
        have hp : (encode.encodeItems sub).length ≤ 55 := by
          by_cases hp : (encode.encodeItems sub).length ≤ 55
          · exact hp
          · have hgt := encode_list_long_length_gt sub (by omega)
            omega
        exact hp)
      -- head = 0xC0 + 0 = 0xC0 when length 1
      have hb' :
          (encode (.list sub))[0]'(by rw [hlen1]; omega) =
            BitVec.ofNat 8 (0xC0 + (encode.encodeItems sub).length) := by
        have h := encode_list_short sub (by
          by_cases hp : (encode.encodeItems sub).length ≤ 55
          · exact hp
          · have hgt := encode_list_long_length_gt sub (by omega)
            omega)
        -- encode_list_short : encode = ofNat (0xC0+n) :: encodeItems
        simpa [h] using encode_head_of_cons h
      have : ((encode (.list sub))[0]'(by rw [hlen1]; omega)).toNat =
          0xC0 + (encode.encodeItems sub).length := by
        rw [hb', BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by
          have : (encode.encodeItems sub).length ≤ 55 := by
            by_cases hp : (encode.encodeItems sub).length ≤ 55
            · exact hp
            · have hgt := encode_list_long_length_gt sub (by omega)
              omega
          omega)
      omega
    · omega
  | bytes data =>
    match data with
    | [] => rfl
    | a :: tail =>
      match tail with
      | [] =>
        by_cases ha : a.toNat < 0x80
        · have henc' : encode (.bytes [a]) = [a] := by
            simp only [encode, encodeBytes, ha, ↓reduceIte]
          have hb' : (encode (.bytes [a]))[0]'(by rw [hlen1]; omega) = a :=
            encode_head_of_cons henc'
          have : a.toNat = ((encode (.bytes [a]))[0]'(by rw [hlen1]; omega)).toNat := by
            rw [hb']
          omega
        · have henc' : encode (.bytes [a]) = [BitVec.ofNat 8 0x81, a] := by
            simp only [encode, encodeBytes, ha, ↓reduceIte]
          have : (encode (.bytes [a])).length = 2 := by simp [henc']
          omega
      | c :: rest =>
        have hne1 : (a :: c :: rest).length ≠ 1 := by intro h; cases h
        by_cases hle55 : (a :: c :: rest).length ≤ 55
        · have hlen2 := encode_bytes_short_ne_one_length (a :: c :: rest) hle55 hne1
          rw [hlen2] at hlen1
          have h0 : (a :: c :: rest).length = 0 := Nat.add_left_cancel hlen1
          cases h0
        · have hgt := encode_bytes_long_length_gt (a :: c :: rest) (by omega)
          rw [hlen1] at hgt
          exact absurd hgt (by decide)

/-- Short-string ante (`0x80 ≤ pfx < 0xb8`) ⇒ content offset in-bounds when either
    the item encode is multi-byte or a following list item exists (empty `0x80`). -/
theorem hss_room_of_short_string_ante
    (txBytes : List (BitVec 8)) (listOff : Nat) (items : List RLPItem) (n : Nat)
    (henc : txBytes.drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : n < items.length)
    (hoff : shortListSrcOff listOff items n < txBytes.length)
    (hlo : ¬ BitVec.ult ((txBytes[shortListSrcOff listOff items n]'hoff).zeroExtend 64)
        (0x80 : Word) = true)
    (hhi : BitVec.ult ((txBytes[shortListSrcOff listOff items n]'hoff).zeroExtend 64)
        (0xb8 : Word) = true)
    (hnext : n + 1 < items.length ∨ 2 ≤ (encode (items[n]'hn)).length) :
    shortListSrcOff listOff items n + 1 < txBytes.length := by
  set srcOff := shortListSrcOff listOff items n
  have hpos : 0 < (encode (items[n]'hn)).length := encode_item_length_pos _
  rcases hnext with hnxt | hge2
  · by_cases hge2' : 2 ≤ (encode (items[n]'hn)).length
    · exact hss_room_of_encode_ge_two txBytes listOff items n henc hshort hn hge2'
    · have hlen1 : (encode (items[n]'hn)).length = 1 := by omega
      have hhead := short_list_item_head_eq txBytes listOff items n henc hshort hn hoff
      have h80 : (0x80 : Word).toNat = 0x80 := by decide
      have hb8 : (0xb8 : Word).toNat = 0xb8 := by decide
      have hze :
          ((txBytes[srcOff]'hoff).zeroExtend 64).toNat =
            (txBytes[srcOff]'hoff).toNat := toNat_zeroExtend_byte _
      have hgeN : 0x80 ≤ (txBytes[srcOff]'hoff).toNat := by
        by_contra hlt
        have hult : BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true := by
          apply (BitVec.ult_iff_lt).2
          change ((txBytes[srcOff]'hoff).zeroExtend 64).toNat < (0x80 : Word).toNat
          rw [hze, h80]; exact Nat.lt_of_not_ge hlt
        exact hlo hult
      have hltN : (txBytes[srcOff]'hoff).toNat < 0xb8 := by
        have hult := (BitVec.ult_iff_lt).1 hhi
        change ((txBytes[srcOff]'hoff).zeroExtend 64).toNat < (0xb8 : Word).toNat at hult
        rwa [hze, hb8] at hult
      have hgeE : 0x80 ≤ ((encode (items[n]'hn))[0]'(by rw [hlen1]; omega)).toNat := by
        simpa [srcOff, hhead] using hgeN
      have hltE : ((encode (items[n]'hn))[0]'(by rw [hlen1]; omega)).toNat < 0xb8 := by
        simpa [srcOff, hhead] using hltN
      have hitem := encode_len1_short_string_is_empty (items[n]'hn) hlen1 hgeE hltE
      exact hss_room_of_empty_not_last txBytes listOff items n henc hshort hn hnxt hitem
  · exact hss_room_of_encode_ge_two txBytes listOff items n henc hshort hn hge2

/-- Packaging `hss` conclusion from room + hover + byte validity. -/
theorem hss_pack_of_room_hover_valid
    (txBytes : List (BitVec 8)) (txBase : Word) (srcOff : Nat)
    (hoff1 : srcOff + 1 < txBytes.length)
    (hover1 : txBase.toNat + (srcOff + 1) < 2 ^ 64)
    (hvalid1 : isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1)) = true) :
    srcOff + 1 < txBytes.length ∧
      txBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
      isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1)) = true :=
  ⟨hoff1, hover1, hvalid1⟩

/-- Fields 0..4 under creation type234 short: `n+1 < items.length` from `6 ≤ length`. -/
theorem extractSuccess_creation_type234_hnext_fields04
    (txBytes : List (BitVec 8))
    (h : extractSuccess txBytes)
    (hcreFlag : (teerExtractToAddress txBytes).2.2 = (1 : Word))
    (hge : 2 ≤ (teerTxTypeDispatch txBytes).2.1.toNat)
    (items : List RLPItem)
    (hdecL : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55) :
    (0 + 1 < items.length) ∧ (1 + 1 < items.length) ∧ (2 + 1 < items.length) ∧
      (3 + 1 < items.length) ∧ (4 + 1 < items.length) := by
  have hlen := extractSuccess_creation_type234_items_length txBytes h hcreFlag hge
    items hdecL hshort
  omega

/-- Packaging `hss` for one short-list item: short-string ante ⇒ room/hover/valid.
    `hnext` discharges empty last-item edge; `hvalid1` is RAM-validity residual. -/
theorem hss_of_short_list_item
    (txBytes : List (BitVec 8)) (txBase : Word) (listOff : Nat)
    (items : List RLPItem) (n : Nat)
    (henc : txBytes.drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : n < items.length)
    (hoff : shortListSrcOff listOff items n < txBytes.length)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hnext : n + 1 < items.length ∨ 2 ≤ (encode (items[n]'hn)).length)
    (hvalid1 : isValidByteAccess
      (txBase + BitVec.ofNat 64 (shortListSrcOff listOff items n + 1)) = true) :
    ¬ BitVec.ult ((txBytes[shortListSrcOff listOff items n]'hoff).zeroExtend 64)
        (0x80 : Word) = true →
      BitVec.ult ((txBytes[shortListSrcOff listOff items n]'hoff).zeroExtend 64)
        (0xb8 : Word) = true →
      shortListSrcOff listOff items n + 1 < txBytes.length ∧
        txBase.toNat + (shortListSrcOff listOff items n + 1) < 2 ^ 64 ∧
        isValidByteAccess
          (txBase + BitVec.ofNat 64 (shortListSrcOff listOff items n + 1)) = true := by
  intro hlo hhi
  have hroom :=
    hss_room_of_short_string_ante txBytes listOff items n henc hshort hn hoff hlo hhi hnext
  have hover1 := hover_of_buffer_span txBase (shortListSrcOff listOff items n + 1)
    txBytes.length hover hroom
  exact hss_pack_of_room_hover_valid txBytes txBase _ hroom hover1 hvalid1

/-- Prefix length of item `n` is strictly before total payload (item nonempty). -/
theorem encodeItemsPrefixLen_lt_total (items : List RLPItem) (n : Nat)
    (hn : n < items.length) :
    encodeItemsPrefixLen items n < (encode.encodeItems items).length := by
  have hpos : 0 < (encode (items[n]'hn)).length := encode_item_length_pos _
  have hdrop := encodeItems_drop_at items n hn
  have hlen := congrArg List.length hdrop
  simp only [List.length_drop, List.length_append] at hlen
  -- length - prefixLen = encode(item) + rest ≥ encode(item) > 0
  have hge : encodeItemsPrefixLen items n ≤ (encode.encodeItems items).length := by
    omega
  have : (encode.encodeItems items).length - encodeItemsPrefixLen items n =
      (encode (items[n]'hn)).length + (encode.encodeItems (items.drop (n + 1))).length := hlen
  omega

/-- Short walk_init cursor = `listOff+1` = `shortListSrcOff 0`. -/
theorem packaging_hcur_shortListSrcOff0
    (txBase : Word) (listOff : Nat) (items : List RLPItem)
    (cursor _endPtr : Word)
    (hc : cursor = txBase + BitVec.ofNat 64 (listOff + 1)) :
    cursor = txBase + BitVec.ofNat 64 (shortListSrcOff listOff items 0) := by
  rwa [shortListSrcOff_zero]

/-- Short-list end pointer: payload end after 1-byte list header. -/
def shortListEndPtr (txBase : Word) (listOff : Nat) (items : List RLPItem) : Word :=
  txBase + BitVec.ofNat 64 (listOff + 1 + (encode.encodeItems items).length)

private theorem toNat_add_ofNat_lt (txBase : Word) (n : Nat)
    (h : txBase.toNat + n < 2 ^ 64) :
    (txBase + BitVec.ofNat 64 n).toNat = txBase.toNat + n := by
  have hn : n < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt h]

/-- `hinb` at short-list end: field cursor strictly before payload end. -/
theorem hinb_short_list_end
    (txBase : Word) (listOff : Nat) (items : List RLPItem) (k : Nat)
    (hn : k < items.length)
    (hover : txBase.toNat + (listOff + 1 + (encode.encodeItems items).length) < 2 ^ 64)
    (endPtr : Word)
    (hend : endPtr = shortListEndPtr txBase listOff items) :
    BitVec.ult (txBase + BitVec.ofNat 64 (shortListSrcOff listOff items k)) endPtr = true := by
  have hlt := encodeItemsPrefixLen_lt_total items k hn
  have hsrc : shortListSrcOff listOff items k =
      listOff + 1 + encodeItemsPrefixLen items k := rfl
  have hendN : endPtr.toNat =
      txBase.toNat + (listOff + 1 + (encode.encodeItems items).length) := by
    rw [hend, shortListEndPtr, toNat_add_ofNat_lt txBase _ hover]
  have hcurN :
      (txBase + BitVec.ofNat 64 (shortListSrcOff listOff items k)).toNat =
        txBase.toNat + shortListSrcOff listOff items k := by
    have hover' : txBase.toNat + shortListSrcOff listOff items k < 2 ^ 64 := by
      simp only [hsrc]; omega
    exact toNat_add_ofNat_lt txBase _ hover'
  apply (BitVec.ult_iff_lt).mpr
  rw [BitVec.lt_def, hcurN, hendN, hsrc]
  omega

/-- Empty field at short-list end ⇒ ∃ `rlpItemDecode` (fit from hinb). -/
theorem hdec_empty_short_list_end
    (txBytes : List (BitVec 8)) (txBase : Word) (listOff : Nat)
    (items : List RLPItem) (k : Nat)
    (henc : txBytes.drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : k < items.length)
    (hoff : shortListSrcOff listOff items k < txBytes.length)
    (hover : txBase.toNat + (listOff + 1 + (encode.encodeItems items).length) < 2 ^ 64)
    (endPtr : Word)
    (hend : endPtr = shortListEndPtr txBase listOff items)
    (hb : txBytes[shortListSrcOff listOff items k]'hoff = (0x80 : BitVec 8)) :
    ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff listOff items k)
        (txBase + BitVec.ofNat 64 (shortListSrcOff listOff items k)) endPtr n l := by
  have hlt := encodeItemsPrefixLen_lt_total items k hn
  have hsrc : shortListSrcOff listOff items k =
      listOff + 1 + encodeItemsPrefixLen items k := rfl
  have hcurN :
      (txBase + BitVec.ofNat 64 (shortListSrcOff listOff items k)).toNat =
        txBase.toNat + shortListSrcOff listOff items k := by
    have hover' : txBase.toNat + shortListSrcOff listOff items k < 2 ^ 64 := by
      simp only [hsrc]; omega
    exact toNat_add_ofNat_lt txBase _ hover'
  have hendN : endPtr.toNat =
      txBase.toNat + (listOff + 1 + (encode.encodeItems items).length) := by
    rw [hend, shortListEndPtr, toNat_add_ofNat_lt txBase _ hover]
  have hle : (txBase + BitVec.ofNat 64 (shortListSrcOff listOff items k)).toNat ≤
      endPtr.toNat := by rw [hcurN, hendN, hsrc]; omega
  have hsub : (endPtr - (txBase + BitVec.ofNat 64 (shortListSrcOff listOff items k))).toNat =
      endPtr.toNat - (txBase + BitVec.ofNat 64 (shortListSrcOff listOff items k)).toNat :=
    BitVec.toNat_sub_of_le hle
  have hfit : BitVec.ult (0 : Word)
      (endPtr - (txBase + BitVec.ofNat 64 (shortListSrcOff listOff items k))) = true := by
    apply (BitVec.ult_iff_lt).mpr
    rw [BitVec.lt_def, hsub, hcurN, hendN, hsrc]
    change 0 < _
    omega
  exact ⟨_, _, rlpItemDecode_empty_short txBytes _ _ endPtr hoff hb hfit⟩

/-- Single-byte prefix `b < 0x80` with fit ⇒ `rlpItemDecode` len=1. -/
theorem rlpItemDecode_single_byte
    (bytes : List (BitVec 8)) (off : Nat) (cursor endPtr : Word)
    (hoff : off < bytes.length)
    (hb : (bytes[off]'hoff).toNat < 0x80)
    (hfit : BitVec.ult cursor endPtr = true) :
    rlpItemDecode bytes off cursor endPtr
      (cursor + signExtend12 (1 : BitVec 12)) (1 : Word) := by
  refine ⟨bytes[off]'hoff, List.getElem?_eq_getElem hoff, Or.inl ?_⟩
  have hze : ((bytes[off]'hoff).zeroExtend 64).toNat = (bytes[off]'hoff).toNat :=
    toNat_zeroExtend_byte _
  have h80 : (0x80 : Word).toNat = 0x80 := by decide
  have hult : BitVec.ult ((bytes[off]'hoff).zeroExtend 64) (0x80 : Word) = true :=
    (BitVec.ult_iff_lt).2 (by
      have : ((bytes[off]'hoff).zeroExtend 64).toNat < 0x80 := by rw [hze]; exact hb
      simpa [BitVec.lt_def, h80] using this)
  exact ⟨hult, hfit, rfl, rfl⟩

/-- Single-byte field at short-list end ⇒ ∃ `rlpItemDecode`. -/
theorem hdec_single_short_list_end
    (txBytes : List (BitVec 8)) (txBase : Word) (listOff : Nat)
    (items : List RLPItem) (k : Nat)
    (_henc : txBytes.drop listOff = encode (.list items))
    (_hshort : (encode.encodeItems items).length ≤ 55)
    (hn : k < items.length)
    (hoff : shortListSrcOff listOff items k < txBytes.length)
    (hover : txBase.toNat + (listOff + 1 + (encode.encodeItems items).length) < 2 ^ 64)
    (endPtr : Word)
    (hend : endPtr = shortListEndPtr txBase listOff items)
    (hb : (txBytes[shortListSrcOff listOff items k]'hoff).toNat < 0x80) :
    ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff listOff items k)
        (txBase + BitVec.ofNat 64 (shortListSrcOff listOff items k)) endPtr n l := by
  have hinb := hinb_short_list_end txBase listOff items k hn hover endPtr hend
  exact ⟨_, _, rlpItemDecode_single_byte txBytes _ _ endPtr hoff hb hinb⟩

/-- Short walk_init end = `shortListEndPtr` under success + short list. -/
theorem short_walk_init_end_eq_shortListEndPtr
    (txBase lenW : Word) (txBytes : List (BitVec 8))
    (items : List RLPItem)
    (h : extractSuccess txBytes)
    (hlenW : lenW.toNat = txBytes.length)
    (hdec : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64) :
    let innerW := (teerTxTypeDispatch txBytes).2.2
    let listOff := innerW.toNat
    let listLen := lenW - innerW
    let listBase := txBase + BitVec.ofNat 64 listOff
    listBase + listLen = shortListEndPtr txBase listOff items := by
  intro innerW listOff listLen listBase
  have hinner : listOff < txBytes.length := extractSuccess_inner_lt txBytes h
  have hlenDrop : listLen.toNat = (txBytes.drop listOff).length :=
    listLen_word_eq_drop txBytes lenW innerW hinner hlenW
  have henc : txBytes.drop listOff = encode (.list items) :=
    decodeListItems_eq_encode _ _ hdec
  have hencLen : (encode (.list items)).length = 1 + (encode.encodeItems items).length :=
    encode_list_short_length items hshort
  have hpay : listLen.toNat = 1 + (encode.encodeItems items).length := by
    rw [hlenDrop, henc, hencLen]
  have hoverEnd : txBase.toNat + (listOff + 1 + (encode.encodeItems items).length) < 2 ^ 64 := by
    have hdropLe : listOff + (txBytes.drop listOff).length ≤ txBytes.length := by
      simp [List.length_drop]; omega
    have : listOff + listLen.toNat ≤ txBytes.length := by
      rw [hlenDrop]; exact hdropLe
    omega
  have hoverBase : txBase.toNat + listOff < 2 ^ 64 := by omega
  have hoverSum : txBase.toNat + listOff + listLen.toNat < 2 ^ 64 := by
    rw [hpay]
    -- associate: a + (b + c) = a + b + c
    simpa [Nat.add_assoc] using hoverEnd
  apply BitVec.eq_of_toNat_eq
  have hlb : listBase.toNat = txBase.toNat + listOff :=
    toNat_add_ofNat_lt txBase listOff hoverBase
  have hl : (listBase + listLen).toNat = txBase.toNat + listOff + listLen.toNat := by
    rw [BitVec.toNat_add, hlb]
    have : listLen.toNat < 2 ^ 64 := listLen.isLt
    omega
  have hr : (shortListEndPtr txBase listOff items).toNat =
      txBase.toNat + (listOff + 1 + (encode.encodeItems items).length) := by
    rw [shortListEndPtr, toNat_add_ofNat_lt txBase _ hoverEnd]
  rw [hl, hr, hpay]
  ac_rfl

/-- Short walk_init cursor = `listBase + 1` = `txBase + shortListSrcOff 0`. -/
theorem short_walk_init_cursor_eq_srcOff0
    (txBase : Word) (listOff : Nat) (items : List RLPItem)
    (hover : txBase.toNat + (listOff + 1) < 2 ^ 64) :
    let listBase := txBase + BitVec.ofNat 64 listOff
    listBase + (1 : Word) =
      txBase + BitVec.ofNat 64 (shortListSrcOff listOff items 0) := by
  intro listBase
  have hover0 : txBase.toNat + listOff < 2 ^ 64 := by omega
  have hse : (1 : Word) = signExtend12 (1 : BitVec 12) := by decide
  apply BitVec.eq_of_toNat_eq
  have hlb : listBase.toNat = txBase.toNat + listOff :=
    toNat_add_ofNat_lt txBase listOff hover0
  have hl : (listBase + (1 : Word)).toNat = txBase.toNat + listOff + 1 := by
    rw [BitVec.toNat_add, hlb]
    have : (1 : Word).toNat = 1 := by decide
    omega
  have hr : (txBase + BitVec.ofNat 64 (shortListSrcOff listOff items 0)).toNat =
      txBase.toNat + (listOff + 1) := by
    rw [shortListSrcOff_zero, toNat_add_ofNat_lt txBase (listOff + 1) hover]
  omega

/-- Package short-path concrete endPtr for of_decode packaging. -/
theorem packaging_short_endPtr
    (txBase lenW : Word) (txBytes : List (BitVec 8))
    (items : List RLPItem)
    (h : extractSuccess txBytes)
    (hlenW : lenW.toNat = txBytes.length)
    (hdec : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64) :
    let innerW := (teerTxTypeDispatch txBytes).2.2
    (txBase + BitVec.ofNat 64 innerW.toNat) + (lenW - innerW) =
      shortListEndPtr txBase innerW.toNat items :=
  short_walk_init_end_eq_shortListEndPtr txBase lenW txBytes items h hlenW hdec hshort hover

/-- `shortWalkCursor` uses `signExtend12 1` = 1. -/
theorem shortWalkCursor_eq_listBase_add1 (txBase : Word) (listOff : Nat) :
    (txBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      (txBase + BitVec.ofNat 64 listOff) + (1 : Word) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]

/-- Machine shortWalkCursor = `txBase + shortListSrcOff 0`. -/
theorem shortWalkCursor_eq_srcOff0
    (txBase : Word) (listOff : Nat) (items : List RLPItem)
    (hover : txBase.toNat + (listOff + 1) < 2 ^ 64) :
    (txBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      txBase + BitVec.ofNat 64 (shortListSrcOff listOff items 0) := by
  rw [shortWalkCursor_eq_listBase_add1]
  exact short_walk_init_cursor_eq_srcOff0 txBase listOff items hover

/-- Machine shortWalkEnd = shortListEndPtr under success + short list. -/
theorem shortWalkEnd_eq_shortListEndPtr
    (txBase lenW : Word) (txBytes : List (BitVec 8))
    (items : List RLPItem)
    (h : extractSuccess txBytes)
    (hlenW : lenW.toNat = txBytes.length)
    (hdec : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64) :
    let innerW := (teerTxTypeDispatch txBytes).2.2
    let listOff := innerW.toNat
    (txBase + BitVec.ofNat 64 listOff) + (lenW - innerW) =
      shortListEndPtr txBase listOff items :=
  packaging_short_endPtr txBase lenW txBytes items h hlenW hdec hshort hover

/-- Remaining bytes from short-list item start to list end (encode item + rest). -/
theorem short_list_remaining_at
    (txBytes : List (BitVec 8)) (listOff : Nat) (items : List RLPItem) (k : Nat)
    (henc : txBytes.drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : k < items.length) :
    (txBytes.drop (shortListSrcOff listOff items k)).length =
      (encode (items[k]'hn)).length +
        (encode.encodeItems (items.drop (k + 1))).length := by
  have hdrop := short_list_item_drop txBytes listOff items k henc hshort hn
  have hlen := congrArg List.length hdrop
  simpa [shortListSrcOff, List.length_append] using hlen

/-- Cursor→end gap at short-list end equals remaining payload from item start. -/
theorem short_list_end_gap
    (txBase : Word) (listOff : Nat) (items : List RLPItem) (k : Nat)
    (hn : k < items.length)
    (hover : txBase.toNat + (listOff + 1 + (encode.encodeItems items).length) < 2 ^ 64)
    (endPtr : Word)
    (hend : endPtr = shortListEndPtr txBase listOff items) :
    let cursor := txBase + BitVec.ofNat 64 (shortListSrcOff listOff items k)
    (endPtr - cursor).toNat =
      (encode.encodeItems items).length - encodeItemsPrefixLen items k := by
  intro cursor
  have hsrc : shortListSrcOff listOff items k =
      listOff + 1 + encodeItemsPrefixLen items k := rfl
  have hprefLt := encodeItemsPrefixLen_lt_total items k hn
  have hover' : txBase.toNat + shortListSrcOff listOff items k < 2 ^ 64 := by
    simp only [hsrc]
    -- prefixLen < total ⇒ listOff+1+prefix < listOff+1+total
    omega
  have hcurN : cursor.toNat = txBase.toNat + shortListSrcOff listOff items k :=
    toNat_add_ofNat_lt txBase _ hover'
  have hendN : endPtr.toNat =
      txBase.toNat + (listOff + 1 + (encode.encodeItems items).length) := by
    rw [hend, shortListEndPtr, toNat_add_ofNat_lt txBase _ hover]
  have hle : cursor.toNat ≤ endPtr.toNat := by
    rw [hcurN, hendN, hsrc]
    omega
  rw [BitVec.toNat_sub_of_le hle, hcurN, hendN, hsrc]
  omega

/-- Short-string (non single-byte) prefix form ⇒ `rlpItemDecode`. -/
theorem rlpItemDecode_short_string
    (bytes : List (BitVec 8)) (off : Nat) (cursor endPtr : Word)
    (data : List Byte)
    (hoff : off < bytes.length)
    (hpfx : bytes[off]'hoff = BitVec.ofNat 8 (0x80 + data.length))
    (hlen : data.length ≤ 55)
    (hnotSingle : ¬ (∃ b : Byte, data = [b] ∧ b.toNat < 0x80))
    (hfit : BitVec.ult (BitVec.ofNat 64 data.length) (endPtr - cursor) = true)
    (hcan : data.length = 1 →
      ∃ c : BitVec 8, bytes[off + 1]? = some c ∧
        ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true) :
    rlpItemDecode bytes off cursor endPtr
      ((cursor + signExtend12 (1 : BitVec 12)) + BitVec.ofNat 64 data.length)
      (BitVec.ofNat 64 data.length) := by
  refine ⟨BitVec.ofNat 8 (0x80 + data.length), ?_, Or.inr (Or.inl ?_)⟩
  · rw [List.getElem?_eq_getElem hoff, hpfx]
  · have hp : (BitVec.ofNat 8 (0x80 + data.length)).toNat = 0x80 + data.length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have hze : ((BitVec.ofNat 8 (0x80 + data.length)).zeroExtend 64).toNat =
        0x80 + data.length := by
      rw [toNat_zeroExtend_byte, hp]
    have h80 : (0x80 : Word).toNat = 0x80 := by decide
    have hb8 : (0xb8 : Word).toNat = 0xb8 := by decide
    have hge : ¬ BitVec.ult
        ((BitVec.ofNat 8 (0x80 + data.length)).zeroExtend 64) (0x80 : Word) = true := by
      intro hult
      have := (BitVec.ult_iff_lt).1 hult
      simp only [BitVec.lt_def, hze, h80] at this
      omega
    have hlt : BitVec.ult
        ((BitVec.ofNat 8 (0x80 + data.length)).zeroExtend 64) (0xb8 : Word) = true :=
      (BitVec.ult_iff_lt).2 (by simp only [BitVec.lt_def, hze, hb8]; omega)
    have hsub :
        (BitVec.ofNat 8 (0x80 + data.length)).zeroExtend 64 - (0x80 : Word) =
          BitVec.ofNat 64 data.length := by
      apply BitVec.eq_of_toNat_eq
      have hle : 0x80 ≤ ((BitVec.ofNat 8 (0x80 + data.length)).zeroExtend 64).toNat := by
        rw [hze]; omega
      rw [BitVec.toNat_sub_of_le hle, hze, h80, BitVec.toNat_ofNat]
      have hd : data.length < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hd]
      omega
    refine ⟨hge, hlt, ?_, ?_, ?_, ?_⟩
    · intro h1
      have hlenW : BitVec.ofNat 64 data.length = (1 : Word) := hsub.symm.trans h1
      have : data.length = 1 := by
        have h1n : (1 : Word).toNat = 1 := by decide
        have := congrArg BitVec.toNat hlenW
        rw [BitVec.toNat_ofNat, h1n, Nat.mod_eq_of_lt (by omega : data.length < 2 ^ 64)] at this
        exact this
      exact hcan this
    · -- fit: ult len (end-cursor)
      rw [hsub]; exact hfit
    · -- next
      rw [hsub]
    · -- len
      exact hsub.symm

/-- Short-list prefix form ⇒ `rlpItemDecode` (len = payload+1 header span). -/
theorem rlpItemDecode_short_list
    (bytes : List (BitVec 8)) (off : Nat) (cursor endPtr : Word)
    (pay : Nat)
    (hoff : off < bytes.length)
    (hpfx : bytes[off]'hoff = BitVec.ofNat 8 (0xC0 + pay))
    (hpay : pay ≤ 55)
    (hfit : ¬ BitVec.ult (endPtr - cursor)
      (BitVec.ofNat 64 pay + signExtend12 (1 : BitVec 12)) = true) :
    rlpItemDecode bytes off cursor endPtr
      (cursor + (BitVec.ofNat 64 pay + signExtend12 (1 : BitVec 12)))
      (BitVec.ofNat 64 pay + signExtend12 (1 : BitVec 12)) := by
  refine ⟨BitVec.ofNat 8 (0xC0 + pay), ?_, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
  · rw [List.getElem?_eq_getElem hoff, hpfx]
  · have hp : (BitVec.ofNat 8 (0xC0 + pay)).toNat = 0xC0 + pay := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have hze : ((BitVec.ofNat 8 (0xC0 + pay)).zeroExtend 64).toNat = 0xC0 + pay := by
      rw [toNat_zeroExtend_byte, hp]
    have hc0 : (0xc0 : Word).toNat = 0xc0 := by decide
    have hf8 : (0xf8 : Word).toNat = 0xf8 := by decide
    have hge : ¬ BitVec.ult
        ((BitVec.ofNat 8 (0xC0 + pay)).zeroExtend 64) (0xc0 : Word) = true := by
      intro hult
      have := (BitVec.ult_iff_lt).1 hult
      simp only [BitVec.lt_def, hze, hc0] at this
      omega
    have hlt : BitVec.ult
        ((BitVec.ofNat 8 (0xC0 + pay)).zeroExtend 64) (0xf8 : Word) = true :=
      (BitVec.ult_iff_lt).2 (by simp only [BitVec.lt_def, hze, hf8]; omega)
    have hsub :
        (BitVec.ofNat 8 (0xC0 + pay)).zeroExtend 64 - (0xc0 : Word) =
          BitVec.ofNat 64 pay := by
      apply BitVec.eq_of_toNat_eq
      have hle : 0xc0 ≤ ((BitVec.ofNat 8 (0xC0 + pay)).zeroExtend 64).toNat := by
        rw [hze]; omega
      rw [BitVec.toNat_sub_of_le hle, hze, hc0, BitVec.toNat_ofNat]
      have hd : pay < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hd]
      omega
    refine ⟨hge, hlt, ?_, ?_, ?_⟩
    · convert hfit using 2
      rw [hsub]
    · rw [hsub]
    · rw [hsub]

/-- Canonicity for short-string len=1: high content byte at `off+1`. -/
theorem short_string_len1_canonicity
    (bytes : List (BitVec 8)) (off : Nat) (data : List Byte) (rest : List Byte)
    (hoff1 : off + 1 < bytes.length)
    (hdrop : bytes.drop off =
      BitVec.ofNat 8 (0x80 + data.length) :: (data ++ rest))
    (hlen1 : data.length = 1)
    (hnotSingle : ¬ (∃ b : Byte, data = [b] ∧ b.toNat < 0x80)) :
    ∃ c : BitVec 8, bytes[off + 1]? = some c ∧
      ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true := by
  obtain ⟨b, hb⟩ : ∃ b, data = [b] := by
    match data with
    | [b] => exact ⟨b, rfl⟩
    | [] => cases hlen1
    | _ :: _ :: _ =>
      simp only [List.length_cons] at hlen1
      omega
  have hbge : ¬ b.toNat < 0x80 := by
    intro hlt
    exact hnotSingle ⟨b, hb, hlt⟩
  have hcons :
      bytes.drop off =
        BitVec.ofNat 8 (0x80 + 1) :: (b :: rest) := by
    simpa [hb, hlen1, List.cons_append, List.nil_append] using hdrop
  have hdrop1 : bytes.drop (off + 1) = b :: rest := by
    have hdd : List.drop 1 (List.drop off bytes) = List.drop (off + 1) bytes := by
      simp [List.drop_drop, Nat.add_assoc]
    have : List.drop 1 (bytes.drop off) = b :: rest := by simp [hcons]
    exact hdd.symm.trans this
  obtain ⟨hoff1', hb1⟩ := getElem_of_drop_cons bytes (off + 1) b rest hdrop1
  have hget : bytes[off + 1]'hoff1 = b := by
    have : bytes[off + 1]'hoff1' = b := hb1
    convert this
  refine ⟨b, ?_, ?_⟩
  · rw [List.getElem?_eq_getElem hoff1, hget]
  · have hze : (b.zeroExtend 64).toNat = b.toNat := toNat_zeroExtend_byte _
    have h80 : (0x80 : Word).toNat = 0x80 := by decide
    intro hult
    have := (BitVec.ult_iff_lt).1 hult
    simp only [BitVec.lt_def, hze, h80] at this
    exact hbge this

/-- Unified: any short-list item admits `rlpItemDecode` at `shortListSrcOff` vs list end. -/
theorem hdec_short_list_item
    (txBytes : List (BitVec 8)) (txBase : Word) (listOff : Nat)
    (items : List RLPItem) (k : Nat)
    (henc : txBytes.drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : k < items.length)
    (hoff : shortListSrcOff listOff items k < txBytes.length)
    (hover : txBase.toNat + (listOff + 1 + (encode.encodeItems items).length) < 2 ^ 64)
    (endPtr : Word)
    (hend : endPtr = shortListEndPtr txBase listOff items) :
    ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff listOff items k)
        (txBase + BitVec.ofNat 64 (shortListSrcOff listOff items k)) endPtr n l := by
  set srcOff := shortListSrcOff listOff items k with hsrc
  set cursor := txBase + BitVec.ofNat 64 srcOff with hcur
  have hitemLen : (encode (items[k]'hn)).length ≤ 55 :=
    encode_item_length_le_55_of_short_list items k hn hshort
  have hdrop := short_list_item_drop txBytes listOff items k henc hshort hn
  have hrem := short_list_remaining_at txBytes listOff items k henc hshort hn
  have hgap := short_list_end_gap txBase listOff items k hn hover endPtr hend
  have hgap' : (endPtr - cursor).toNat =
      (encode (items[k]'hn)).length +
        (encode.encodeItems (items.drop (k + 1))).length := by
    have hpref := encodeItems_drop_at items k hn
    have hlen := congrArg List.length hpref
    simp only [List.length_drop, List.length_append] at hlen
    have hsrc' : srcOff = listOff + 1 + encodeItemsPrefixLen items k := by
      simp only [srcOff, shortListSrcOff]
    -- gap = total - prefix = encode item + rest
    have : (encode.encodeItems items).length - encodeItemsPrefixLen items k =
        (encode (items[k]'hn)).length +
          (encode.encodeItems (items.drop (k + 1))).length := by
      have hge : encodeItemsPrefixLen items k ≤ (encode.encodeItems items).length := by
        have hlt := encodeItemsPrefixLen_lt_total items k hn
        omega
      omega
    simpa [cursor, srcOff, hsrc', this] using hgap
  cases hitem : items[k]'hn with
  | bytes data =>
    by_cases hsingle : ∃ b : Byte, data = [b] ∧ b.toNat < 0x80
    · obtain ⟨b, hbdata, hblt⟩ := hsingle
      have hencI : encode (items[k]'hn) = [b] := by
        rw [hitem, hbdata, encode_bytes_single b hblt]
      have hdrop' : txBytes.drop srcOff = b :: encode.encodeItems (items.drop (k + 1)) := by
        have : encode (items[k]'hn) = [b] := hencI
        simpa [srcOff, shortListSrcOff, this, List.cons_append, List.nil_append] using hdrop
      obtain ⟨hoff', hb⟩ := getElem_of_drop_cons txBytes srcOff b _ hdrop'
      have hinb := hinb_short_list_end txBase listOff items k hn hover endPtr hend
      refine ⟨_, _, rlpItemDecode_single_byte txBytes srcOff cursor endPtr hoff' ?_ ?_⟩
      · rw [hb]; exact hblt
      · simpa [cursor, srcOff] using hinb
    · -- short-string path (empty / high single / multi ≤55)
      have hdataLe : data.length ≤ 55 :=
        bytes_data_length_le_55_of_encode_le data (by simpa [hitem] using hitemLen) hsingle
      have hencI := encode_bytes_short_string data hdataLe hsingle
      have hdrop' :
          txBytes.drop srcOff =
            BitVec.ofNat 8 (0x80 + data.length) ::
              (data ++ encode.encodeItems (items.drop (k + 1))) := by
        have : encode (items[k]'hn) =
            [BitVec.ofNat 8 (0x80 + data.length)] ++ data := by
          rw [hitem, hencI]
        simpa [srcOff, shortListSrcOff, this, List.cons_append] using hdrop
      obtain ⟨hoff', hb⟩ :=
        getElem_of_drop_cons txBytes srcOff (BitVec.ofNat 8 (0x80 + data.length)) _ hdrop'
      have hencLen : (encode (items[k]'hn)).length = 1 + data.length := by
        rw [hitem, encode_bytes_short_string_length data hdataLe hsingle]
      have hgapN : (endPtr - cursor).toNat = 1 + data.length +
          (encode.encodeItems (items.drop (k + 1))).length := by
        simpa [hencLen] using hgap'
      have hfit : BitVec.ult (BitVec.ofNat 64 data.length) (endPtr - cursor) = true := by
        apply (BitVec.ult_iff_lt).mpr
        rw [BitVec.lt_def, BitVec.toNat_ofNat]
        have hd : data.length < 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt hd, hgapN]
        omega
      have hcan : data.length = 1 →
          ∃ c : BitVec 8, txBytes[srcOff + 1]? = some c ∧
            ¬ BitVec.ult (c.zeroExtend 64) (0x80 : Word) = true := by
        intro hlen1
        have hoff1 : srcOff + 1 < txBytes.length := by
          have hrem' : (txBytes.drop srcOff).length = 1 + data.length +
              (encode.encodeItems (items.drop (k + 1))).length := by
            simpa [srcOff, hencLen] using hrem
          rw [List.length_drop] at hrem'
          omega
        -- drop form for canonicity
        exact short_string_len1_canonicity txBytes srcOff data
          (encode.encodeItems (items.drop (k + 1))) hoff1 hdrop' hlen1 hsingle
      exact ⟨_, _, rlpItemDecode_short_string txBytes srcOff cursor endPtr data
        hoff' hb hdataLe hsingle hfit hcan⟩
  | list sub =>
    have hencLen : (encode (.list sub)).length ≤ 55 := by simpa [hitem] using hitemLen
    obtain ⟨hpayLe, hencForm⟩ := encode_list_of_encode_le_55 sub hencLen
    set pay := (encode.encodeItems sub).length with hpay_def
    have hpayLe' : pay ≤ 55 := by simpa [hpay_def] using hpayLe
    have hdrop' :
        txBytes.drop srcOff =
          BitVec.ofNat 8 (0xC0 + pay) ::
            (encode.encodeItems sub ++ encode.encodeItems (items.drop (k + 1))) := by
      have : encode (items[k]'hn) =
          BitVec.ofNat 8 (0xC0 + pay) :: encode.encodeItems sub := by
        rw [hitem, hencForm, hpay_def]
      simpa [srcOff, shortListSrcOff, this, List.cons_append] using hdrop
    obtain ⟨hoff', hb⟩ :=
      getElem_of_drop_cons txBytes srcOff (BitVec.ofNat 8 (0xC0 + pay)) _ hdrop'
    have hencLen' : (encode (items[k]'hn)).length = 1 + pay := by
      have : encode (items[k]'hn) =
          BitVec.ofNat 8 (0xC0 + pay) :: encode.encodeItems sub := by
        rw [hitem, hencForm, hpay_def]
      simp only [this, List.length_cons, hpay_def]
      omega
    have hgapN : (endPtr - cursor).toNat = 1 + pay +
        (encode.encodeItems (items.drop (k + 1))).length := by
      simpa [hencLen'] using hgap'
    have hse : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
    have hspanN : (BitVec.ofNat 64 pay + signExtend12 (1 : BitVec 12)).toNat = pay + 1 := by
      rw [hse, BitVec.toNat_add, BitVec.toNat_ofNat]
      have hp : pay < 2 ^ 64 := by omega
      have h1 : (1 : Word).toNat = 1 := by decide
      rw [Nat.mod_eq_of_lt hp, h1]
      omega
    have hfit : ¬ BitVec.ult (endPtr - cursor)
        (BitVec.ofNat 64 pay + signExtend12 (1 : BitVec 12)) = true := by
      intro hult
      have := (BitVec.ult_iff_lt).1 hult
      simp only [BitVec.lt_def, hspanN] at this
      omega
    exact ⟨_, _, rlpItemDecode_short_list txBytes srcOff cursor endPtr pay
      hoff' hb hpayLe' hfit⟩

/-- Packaging: `hdec` at shortWalkEnd for field `k` under short list. -/
theorem hdec_short_list_end
    (txBytes : List (BitVec 8)) (txBase : Word) (listOff : Nat)
    (items : List RLPItem) (k : Nat)
    (henc : txBytes.drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : k < items.length)
    (hoff : shortListSrcOff listOff items k < txBytes.length)
    (hover : txBase.toNat + (listOff + 1 + (encode.encodeItems items).length) < 2 ^ 64)
    (endPtr : Word)
    (hend : endPtr = shortListEndPtr txBase listOff items) :
    ∃ n l : Word,
      rlpItemDecode txBytes (shortListSrcOff listOff items k)
        (txBase + BitVec.ofNat 64 (shortListSrcOff listOff items k)) endPtr n l :=
  hdec_short_list_item txBytes txBase listOff items k henc hshort hn hoff hover endPtr hend

#print axioms encode_item_length_pos
#print axioms shortListSrcOff_lt_length
#print axioms extractSuccess_creation_type234_hoff_srcOff
#print axioms extractSuccess_creation_type234_hover_srcOff
#print axioms short_list_item_head_eq
#print axioms hss_room_of_encode_ge_two
#print axioms hss_room_of_empty_not_last
#print axioms encode_item_head_toNat_bounds
#print axioms encode_item_head_not_long_string
#print axioms encode_item_head_lt_f8
#print axioms hls_vacuous_of_short_list_item
#print axioms hll_vacuous_of_short_list_item
#print axioms hss_room_of_short_string_ante
#print axioms hss_of_short_list_item
#print axioms extractSuccess_creation_type234_hnext_fields04
#print axioms encodeItemsPrefixLen_lt_total
#print axioms packaging_hcur_shortListSrcOff0
#print axioms hinb_short_list_end
#print axioms hdec_empty_short_list_end
#print axioms rlpItemDecode_single_byte
#print axioms hdec_single_short_list_end
#print axioms short_walk_init_end_eq_shortListEndPtr
#print axioms short_walk_init_cursor_eq_srcOff0
#print axioms packaging_short_endPtr
#print axioms shortWalkCursor_eq_listBase_add1
#print axioms shortWalkCursor_eq_srcOff0
#print axioms shortWalkEnd_eq_shortListEndPtr
#print axioms short_list_remaining_at
#print axioms short_list_end_gap
#print axioms rlpItemDecode_short_string
#print axioms rlpItemDecode_short_list
#print axioms short_string_len1_canonicity
#print axioms hdec_short_list_item
#print axioms hdec_short_list_end

end EvmAsm.Codegen.TxExtractToAddressHonesty
