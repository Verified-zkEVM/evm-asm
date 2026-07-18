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

end EvmAsm.Codegen.TxExtractToAddressHonesty
