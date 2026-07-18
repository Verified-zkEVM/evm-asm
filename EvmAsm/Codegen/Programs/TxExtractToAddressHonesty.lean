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

#print axioms rlpItemDecode_empty_short
#print axioms rlpWalkNextOk_empty_short
#print axioms rlpItemDecode_addr20_short
#print axioms decodeListItems_eq_encode
#print axioms decodeListItems_short_walkInit_guards
#print axioms extractSuccess_inner_eq_encode

end EvmAsm.Codegen.TxExtractToAddressHonesty
