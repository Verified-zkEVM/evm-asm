/-
  EvmAsm.Rv64.RLP.UnifiedScalarFieldDecode

  EL.3 / Phase 5 — full SCALAR FIELD decode. Composes the single-item decoder
  (`unified_list_header_descend`, which leaves a field's payload pointer in `x13`
  and length in `x11`) with the big-endian value read (`unified_field_scalar_read`)
  so a `.bytes` scalar field is decoded end-to-end from its offset, and proves
  coincidence with the pure `decodeScalar`. The per-field unit the fixed-schema STF
  header/tx decoders walk.
-/

import EvmAsm.Rv64.RLP.UnifiedListDescendConcrete
import EvmAsm.Rv64.RLP.UnifiedFieldScalarRead
import EvmAsm.EL.RLP.Scalar

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

private theorem toNat_ofNat8 {k : Nat} (h : k < 256) : (BitVec.ofNat 8 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simpa using h)]

/-- Short `.bytes` encoding in uniform `[0x80 + len] ++ data` form, for any data
    that is NOT a single byte `< 0x80` (i.e. excluding the `.singleByte` case). -/
private theorem encodeBytes_shortBytes_form (data : List Byte) (hlen55 : data.length ≤ 55)
    (hns : ¬ ∃ b, data = [b] ∧ b.toNat < 0x80) :
    encode (.bytes data) = [BitVec.ofNat 8 (0x80 + data.length)] ++ data := by
  rcases data with _ | ⟨b, _ | ⟨c, rest⟩⟩
  · simp [encode, encodeBytes_nil]
  · have hb : ¬ b.toNat < 0x80 := fun h => hns ⟨b, rfl, h⟩
    rw [encode, encodeBytes_single_large b hb]
    simp only [List.length_singleton, List.cons_append, List.nil_append]
  · rw [encode, encodeBytes_short_of_length_ne_one _ hlen55 (by simp)]

/-- **`.bytes`-item payload window** (the `.bytes` analog of `list_item_payload_window`).
    For a short `.bytes data` item at byte offset `off` of the region, the single-item
    decoder's window — `itemPtrRegion` (the `x13` payload pointer) and `itemLenRegion`
    (the `x11` payload length) — points exactly at `data`. -/
theorem bytes_item_payload_window (data : List Byte) (tail : List Byte)
    (regionBase : Word) (off : Nat) (bs : List Byte)
    (hdrop : bs.drop off = encode (.bytes data) ++ tail)
    (hlen55 : data.length ≤ 55) :
    ∃ payloadOff,
      itemPtrRegion ((encode (.bytes data))[0]'(encode_nonempty _)) regionBase off
        = regionBase + BitVec.ofNat 64 payloadOff
      ∧ itemLenRegion ((encode (.bytes data))[0]'(encode_nonempty _)) bs off
        = BitVec.ofNat 64 data.length
      ∧ bs.drop payloadOff = data ++ tail := by
  by_cases hsingle : ∃ b, data = [b] ∧ b.toNat < 0x80
  · -- singleByte: encoding is the byte itself; payload starts at `off`
    obtain ⟨b, rfl, hb⟩ := hsingle
    have henc : encode (.bytes [b]) = [b] := encodeBytes_single_small b hb
    have hhead : (encode (.bytes [b]))[0]'(encode_nonempty _) = b := by simp [henc]
    have hcls : classifyPrefix ((encode (.bytes [b]))[0]'(encode_nonempty _)) = .singleByte := by
      rw [hhead, classifyPrefix_singleByte_iff]; exact hb
    refine ⟨off, ?_, ?_, ?_⟩
    · simp only [itemPtrRegion, hcls]
    · simp only [itemLenRegion, hcls, List.length_singleton]; rfl
    · rw [hdrop, henc]
  · -- shortBytes: header is one prefix byte; payload starts at `off + 1`
    have henc := encodeBytes_shortBytes_form data hlen55 hsingle
    have hhead : (encode (.bytes data))[0]'(encode_nonempty _)
        = BitVec.ofNat 8 (0x80 + data.length) := by simp [henc]
    have hcls : classifyPrefix ((encode (.bytes data))[0]'(encode_nonempty _)) = .shortBytes := by
      rw [hhead, classifyPrefix_shortBytes_iff, toNat_ofNat8 (by omega)]; omega
    refine ⟨off + 1, ?_, ?_, ?_⟩
    · simp only [itemPtrRegion, hcls]
    · simp only [itemLenRegion, hcls]
      rw [hhead, rlpPrefixShortBytesPayloadLen, toNat_ofNat8 (by omega),
        show 0x80 + data.length - 0x80 = data.length from by omega]
    · have hdd : bs.drop (off + 1) = (bs.drop off).drop 1 := by rw [List.drop_drop]
      rw [hdd, hdrop, henc]
      simp only [List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero]

end EvmAsm.Rv64.RLP
