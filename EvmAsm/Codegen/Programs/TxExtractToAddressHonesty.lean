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

end EvmAsm.Codegen.TxExtractToAddressHonesty
