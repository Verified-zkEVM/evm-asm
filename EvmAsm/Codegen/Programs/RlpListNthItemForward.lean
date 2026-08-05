/-
  EvmAsm.Codegen.Programs.RlpListNthItemForward

  Forward (model → guest) construction of `rlp_list_nth_item`'s success
  predicate.  `Success` / `StrictListPayload` / `StrictNthItem` previously had
  **no constructor at all** driven by a model-side decode — every lemma about
  them consumed one.  That gap is the shared prerequisite behind #11351,
  #11345 and #11346.

  Lives under `Codegen` rather than beside `Rv64/RLP/ItemDecodeForward.lean`
  because `StrictNthItem` and friends are Codegen-layer definitions and
  `scripts/check-layering.sh` L1 forbids core importing Codegen — the same
  split used for the determinism prerequisite in #11408.

  Scope is byte-string children, inherited from `ItemDecodeForward`: the
  converse direction is false for nested lists (`c3 c2 81 00`), and every RLP
  field of a block header is a byte string.
-/

import EvmAsm.Codegen.Programs.RlpListNthItemSAsmBase
import EvmAsm.Rv64.RLP.ItemDecodeForward

namespace EvmAsm.Codegen.RlpListNthItemSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP

/-! ## The selected child -/

/-- From a byte-string `DecodeChain` covering the list payload, the guest's
    `StrictNthItem` holds for whichever child the model put at `index`.

    Induction is on `index`, generalising the item list and the start offset:
    the head decode supplies one `rlpItemDecode`, and the tail supplies the
    rest of the chain re-entered at `(next - base).toNat`. -/
theorem strictNthItem_of_chain
    (bytes : List Byte) (base : Word) (endOff : Nat)
    (hendOff : endOff ≤ bytes.length) (hover : base.toNat + bytes.length < 2 ^ 64) :
    ∀ (index : Nat) (items : List RLPItem) (off offEnd : Nat) (p : List Byte),
      DecodeChain bytes off items offEnd → offEnd ≤ endOff →
      (∀ it ∈ items, ∃ q, it = RLPItem.bytes q) →
      items[index]? = some (RLPItem.bytes p) →
      ∃ next off', next = base + BitVec.ofNat 64 off' ∧
        StrictNthItem bytes base (base + BitVec.ofNat 64 endOff) index off next
          (BitVec.ofNat 64 p.length) ∧
        (bytes.drop (off' - p.length)).take p.length = p ∧ p.length ≤ off' ∧
        off' ≤ endOff := by
  intro index
  induction index with
  | zero =>
      intro items off offEnd p hchain hle hbytes hidx
      cases items with
      | nil => simp at hidx
      | cons item rest =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hidx
          subst hidx
          obtain ⟨off', hdec, hrest⟩ := hchain
          have hoff'le : off' ≤ offEnd :=
            DecodeChain.le_of_bytes rest off' offEnd hrest (by omega)
              (fun it hit => hbytes it (List.mem_cons_of_mem _ hit))
          refine ⟨base + BitVec.ofNat 64 off', off', rfl, ?_, ?_⟩
          · exact .zero off _ _
              (rlpItemDecode_of_decodeAux_bytes bytes base off off' endOff 0 p
                (hdec 0) (by omega) hendOff hover)
          · obtain ⟨hc, hb⟩ := decodeAux_bytes_content bytes off off' 0 p (hdec 0) (by omega)
            exact ⟨hc, by omega, by omega⟩
  | succ index ih =>
      intro items off offEnd p hchain hle hbytes hidx
      cases items with
      | nil => simp at hidx
      | cons item rest =>
          simp only [List.getElem?_cons_succ] at hidx
          obtain ⟨off', hdec, hrest⟩ := hchain
          obtain ⟨q, hq⟩ := hbytes item (List.mem_cons_self ..)
          subst hq
          have hoff'le : off' ≤ offEnd :=
            DecodeChain.le_of_bytes rest off' offEnd hrest (by omega)
              (fun it hit => hbytes it (List.mem_cons_of_mem _ hit))
          have hhead := rlpItemDecode_of_decodeAux_bytes bytes base off off' endOff 0 q
            (hdec 0) (by omega) hendOff hover
          have hrec := ih rest off' offEnd p hrest hle
            (fun it hit => hbytes it (List.mem_cons_of_mem _ hit)) hidx
          have hback : ((base + BitVec.ofNat 64 off') - base).toNat = off' :=
            sub_base_of_base_add (bound := bytes.length) (by omega) hover
          obtain ⟨next, off'', hnexteq, h, hcont, hple, hoe⟩ := hrec
          refine ⟨next, off'', hnexteq, ?_, hcont, hple, hoe⟩
          exact .succ index off _ _ _ _ hhead (by rw [hback]; exact h)

/-! ## The outer list header -/

/-- Long-list header (`0xF8..0xFF`), forward.  This is the shape a block
    header takes: ~500 bytes of payload means a `0xF9` prefix with two length
    bytes. -/
theorem strictListPayload_long_forward
    (bytes : List Byte) (base : Word) (b : Byte) (lol payloadLen : Nat)
    (hbyte : bytes[0]? = some b)
    (hlong : 0xF8 ≤ b.toNat)
    (hlolDef : lol = b.toNat - 0xF7)
    (hfirst : ∃ first : Byte, bytes[1]? = some first ∧ first ≠ 0)
    (hpayLen : Nat.fromBytesBE ((bytes.drop 1).take lol) = payloadLen)
    (hminimal : 56 ≤ payloadLen) :
    StrictListPayload bytes base (1 + lol + payloadLen) (1 + lol)
      (base + BitVec.ofNat 64 (1 + lol + payloadLen)) := by
  obtain ⟨first, hfirstGet, hfirstNz⟩ := hfirst
  have hb256 : b.toNat < 256 := b.isLt
  have hlolNat : (b.zeroExtend 64 - (0xf7 : Word)).toNat = lol := by
    have hw : b.zeroExtend 64 - (0xf7 : Word) = BitVec.ofNat 64 lol := by
      rw [show (0xf7 : Word) = BitVec.ofNat 64 0xf7 from by decide]
      exact zeroExtend_sub_eq_ofNat (by omega) hlolDef (by norm_num)
    rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnotlt : ¬ BitVec.ult (b.zeroExtend 64) (0xf8 : Word) = true := by
    rw [show (0xf8 : Word) = BitVec.ofNat 64 0xf8 from by decide]
    exact fun hc => absurd ((ult_zeroExtend_iff (by norm_num)).mp hc) (by omega)
  exact .long (1 + lol + payloadLen) (1 + lol) b first hbyte hnotlt hfirstGet hfirstNz
    (by rw [hlolNat, hpayLen]; exact hminimal)
    (by rw [hlolNat])
    (by rw [hlolNat, hpayLen])

/-- Short-list header (`0xC0..0xF7`), forward. -/
theorem strictListPayload_short_forward
    (bytes : List Byte) (base : Word) (b : Byte) (payloadLen : Nat)
    (hbyte : bytes[0]? = some b)
    (hlo : 0xC0 ≤ b.toNat) (hhi : b.toNat < 0xF8)
    (hpay : payloadLen = b.toNat - 0xC0) :
    StrictListPayload bytes base (payloadLen + 1) 1
      (base + BitVec.ofNat 64 (payloadLen + 1)) := by
  have hb256 : b.toNat < 256 := b.isLt
  have hlenNat : (b.zeroExtend 64 - (0xc0 : Word)).toNat = payloadLen := by
    have hw : b.zeroExtend 64 - (0xc0 : Word) = BitVec.ofNat 64 payloadLen := by
      rw [show (0xc0 : Word) = BitVec.ofNat 64 0xc0 from by decide]
      exact zeroExtend_sub_eq_ofNat (by omega) hpay (by norm_num)
    rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine .short (payloadLen + 1) 1 b hbyte ?_ ?_ rfl (by rw [hlenNat])
  · rw [show (0xc0 : Word) = BitVec.ofNat 64 0xc0 from by decide]
    exact fun hc => absurd ((ult_zeroExtend_iff (by norm_num)).mp hc) (by omega)
  · rw [show (0xf8 : Word) = BitVec.ofNat 64 0xf8 from by decide]
    exact (ult_zeroExtend_iff (by norm_num)).mpr (by omega)

/-! ## Assembling `Success` -/

/-- The full forward construction: a model-side list decode whose children are
    all byte strings yields the guest's `Success` for any child index the model
    provides.  `listLen` is the **complete** encoded length (header + payload),
    matching `StrictListPayload`'s index. -/
theorem success_forward
    (bytes : List Byte) (base : Word) (listLen cursorOff index : Nat)
    (items : List RLPItem) (p : List Byte)
    (hpayload : StrictListPayload bytes base listLen cursorOff
      (base + BitVec.ofNat 64 listLen))
    (hchain : DecodeChain bytes cursorOff items listLen)
    (hbytes : ∀ it ∈ items, ∃ q, it = RLPItem.bytes q)
    (hidx : items[index]? = some (RLPItem.bytes p))
    (hlistLen : listLen ≤ bytes.length)
    (hover : base.toNat + bytes.length < 2 ^ 64) :
    ∃ offset, Success bytes base listLen index offset (BitVec.ofNat 64 p.length) := by
  obtain ⟨next, -, -, h, -, -, -⟩ := strictNthItem_of_chain bytes base listLen hlistLen hover
    index items cursorOff listLen p hchain (le_refl _) hbytes hidx
  exact ⟨_, cursorOff, base + BitVec.ofNat 64 listLen, next, hpayload, h, rfl⟩

/-! ## Non-vacuity

End-to-end on a concrete buffer: `c4 83 01 02 03` is a four-byte-payload list
holding one three-byte string.  Both the header lemma and the chain feed
`success_forward`, so the whole composition is demonstrably instantiable — the
hypothesis set is satisfiable, not merely consistent. -/

set_option maxRecDepth 8000 in
example :
    ∃ offset, Success [0xc4, 0x83, 0x01, 0x02, 0x03] (0x1000 : Word) 5 0 offset
      (BitVec.ofNat 64 3) := by
  refine success_forward [0xc4, 0x83, 0x01, 0x02, 0x03] (0x1000 : Word) 5 1 0
    [RLPItem.bytes [0x01, 0x02, 0x03]] [0x01, 0x02, 0x03]
    (strictListPayload_short_forward _ _ 0xc4 4 rfl (by decide) (by decide) (by decide))
    ⟨5, fun _ => rfl, rfl⟩ ?_ rfl (by norm_num) (by decide)
  intro it hit
  simp only [List.mem_singleton] at hit
  exact ⟨[0x01, 0x02, 0x03], hit⟩

end EvmAsm.Codegen.RlpListNthItemSAsm
