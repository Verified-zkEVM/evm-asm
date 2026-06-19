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

set_option maxRecDepth 8000 in
/-- **Full scalar field decode.** From `x13 = regionBase + ofNat O` (a `.bytes data`
    scalar field at offset `O`, `1 ≤ data.length ≤ 8`), the program decodes the item
    header then reads the payload big-endian, leaving `x11 = Nat.fromBytesBE data`
    (the field value) and `x13` at the next field — coinciding with the pure
    `decodeScalar (bs.drop O) = some (Nat.fromBytesBE data, tail)`. -/
theorem unified_scalar_field_decode
    (base regionBase : Word) (bs : List Byte) (O : Nat) (data : List Byte) (tail : List Byte)
    (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (hlen1 : 1 ≤ data.length) (hlen8 : data.length ≤ 8)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdrop : bs.drop O = encode (.bytes data) ++ tail) :
    cpsTripleWithin (61 + (2 + 6 * data.length)) base (base + 180)
      (((CodeReq.singleton base (.LBU .x5 .x13 0)).union
          (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
          (((CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0)).union
              (CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0))).union
              (CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20)))))
      ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs)
      (((.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE data)) **
        (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes data)).length))) **
        regOwn .x14 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs) **
       (regOwn .x5 ** regOwn .x10 ** (.x15 ↦ᵣ v15Old)))
    ∧ decodeScalar (bs.drop O) = some (Nat.fromBytesBE data, tail) := by
  have hbs0 : O < bs.length := by
    have h := congrArg List.length hdrop
    rw [List.length_drop, List.length_append] at h
    have := encode_nonempty (RLPItem.bytes data); omega
  have hbs_head : bs[O]'hbs0 = (encode (.bytes data))[0]'(encode_nonempty (RLPItem.bytes data)) := by
    have key : (bs.drop O)[0]'(by rw [List.length_drop]; omega)
        = (encode (.bytes data))[0]'(encode_nonempty (RLPItem.bytes data)) :=
      (List.getElem_of_eq hdrop _).trans (List.getElem_append_left (encode_nonempty _))
    rw [← key]; simp
  obtain ⟨payloadOff, hptr, hlen, hpay⟩ :=
    bytes_item_payload_window data tail regionBase O bs hdrop (by omega)
  rw [show ((encode (.bytes data))[0]'(encode_nonempty (RLPItem.bytes data)))
        = (bs[O]'hbs0) from hbs_head.symm] at hptr hlen
  have hsize' : (encode (.bytes data)).length < 256 ^ 8 := by
    have hle : (encode (.bytes data)).length ≤ data.length + 1 := by
      by_cases hs : ∃ b, data = [b] ∧ b.toNat < 0x80
      · obtain ⟨b, rfl, hb⟩ := hs
        rw [show encode (.bytes [b]) = [b] from encodeBytes_single_small b hb]; omega
      · rw [encodeBytes_shortBytes_form data (by omega) hs]
        simp only [List.length_append, List.length_singleton]; omega
    have h9 : data.length + 1 ≤ 9 := by omega
    calc (encode (.bytes data)).length ≤ 9 := le_trans hle h9
      _ < 256 ^ 8 := by norm_num
  have hpay_take : (bs.drop payloadOff).take data.length = data := by
    rw [hpay, List.take_left' rfl]
  have hstride : payloadOff + data.length = O + (encode (.bytes data)).length := by
    have e1 := congrArg List.length hpay
    have e2 := congrArg List.length hdrop
    simp only [List.length_drop, List.length_append] at e1 e2; omega
  have hwin' : ∀ i, i < data.length →
      payloadOff + i < bs.length
      ∧ isValidByteAccess (regionBase + BitVec.ofNat 64 (payloadOff + i)) = true := by
    intro i hi
    have hb : payloadOff + i < bs.length := by
      have e1 := congrArg List.length hpay
      rw [List.length_drop, List.length_append] at e1; omega
    exact ⟨hb, hwin _ hb⟩
  have hwindow0 : regionLongWindow regionBase bs O hbs0 :=
    regionLongWindow_of_split regionBase bs (.bytes data) tail O hbs0 hbs_head hdrop
      (by simpa [itemPayloadCount] using (show data.length < 256 ^ 8 by omega)) hwin
  have hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 O) = true := hwin O hbs0
  -- t_hdr : LBU + decoder  (item header → x13 = itemPtrRegion, x11 = itemLenRegion)
  have t_hdr := unified_list_header_descend base regionBase bs O hbs0
    v5Old v10 v11Old v12Old v14Old v15Old halign hover hvalid0 hwindow0
  -- t_read : the field scalar read (framed with the untouched x5/x10/x15)
  have read_raw := unified_field_scalar_read (base + 148) regionBase bs payloadOff data.length
    (itemX12Region (bs[O]'hbs0) bs O v12Old) (itemX14 (bs[O]'hbs0) v14Old)
    hlen1 hlen8 halign hover hwin'
  rw [show base + 148 + 4 = base + 152 from by bv_omega,
      show base + 148 + 8 = base + 156 from by bv_omega,
      show base + 148 + 32 = base + 180 from by bv_omega] at read_raw
  have s_read : cpsTripleWithin (2 + 6 * data.length) (base + 148) (base + 180)
      (((CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0)).union
          (CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0))).union
          (CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20))))
      ((.x5 ↦ᵣ (bs[O]'hbs0).zeroExtend 64) ** (.x0 ↦ᵣ (0:Word)) **
       (.x10 ↦ᵣ itemResidue (bs[O]'hbs0)) ** (.x11 ↦ᵣ itemLenRegion (bs[O]'hbs0) bs O) **
       (.x12 ↦ᵣ itemX12Region (bs[O]'hbs0) bs O v12Old) **
       (.x13 ↦ᵣ itemPtrRegion (bs[O]'hbs0) regionBase O) **
       (.x14 ↦ᵣ itemX14 (bs[O]'hbs0) v14Old) ** (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs)
      (((.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE data)) **
        (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes data)).length))) **
        regOwn .x14 ** regOwn .x12 ** (.x0 ↦ᵣ (0:Word)) ** bytesRegion regionBase bs) **
       (regOwn .x5 ** regOwn .x10 ** (.x15 ↦ᵣ v15Old))) :=
    cpsTripleWithin_weaken
      (fun _ hp => by rw [hlen, hptr] at hp; xperm_hyp hp)
      (fun h hp => by
        rw [hpay_take, show regionBase + BitVec.ofNat 64 (payloadOff + data.length)
              = regionBase + BitVec.ofNat 64 (O + (encode (.bytes data)).length)
            from by rw [hstride]] at hp
        exact sepConj_mono
          (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono (regIs_implies_regOwn _)
              (sepConj_mono (regIs_implies_regOwn _) (fun _ x => x)))))
          (sepConj_mono (regIs_implies_regOwn _)
            (sepConj_mono (regIs_implies_regOwn _) (fun _ x => x)))
          h hp)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ (bs[O]'hbs0).zeroExtend 64) ** (.x10 ↦ᵣ itemResidue (bs[O]'hbs0)) **
         (.x15 ↦ᵣ v15Old))
        (by pcFree) read_raw)
  have dcr_none4 : ∀ (a : Word),
      (∀ k, k < 36 → a ≠ (base + 4) + BitVec.ofNat 64 (4 * k)) →
      CodeReq.ofProg (base + 4) unified_decoder_prog a = none :=
    fun a h => CodeReq.ofProg_none_range_len (base + 4) unified_decoder_prog 36 a
      unified_decoder_prog_length h
  have hd : ((CodeReq.singleton base (.LBU .x5 .x13 0)).union
        (CodeReq.ofProg (base + 4) unified_decoder_prog)).Disjoint
      (((CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0)).union
          (CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0))).union
          (CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20)))) :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton (by bv_omega))
          (CodeReq.Disjoint.singleton (by bv_omega)))
        (CodeReq.Disjoint.singleton_ofProg
          (CodeReq.ofProg_none_range_len (base + 156) (rlp_phase2_long_loop_body_prog (-20)) 6 base
            (by rfl) (by intro k hk; bv_omega))))
      (CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.ofProg_singleton (dcr_none4 (base + 148) (by intro k hk; bv_omega)))
          (CodeReq.Disjoint.ofProg_singleton (dcr_none4 (base + 152) (by intro k hk; bv_omega))))
        (ofProg_disjoint_ofProg (base + 4) (base + 156) _ _ 36 6
          unified_decoder_prog_length (by rfl) (by intro k1 hk1 k2 hk2; bv_omega)))
  refine ⟨cpsTripleWithin_seq hd t_hdr s_read, ?_⟩
  rw [hdrop]
  unfold decodeScalar
  rw [decode_encode_append (.bytes data) tail hsize']
  rfl

-- Concrete cross-check: decode the single-byte scalar `0x2a` (= 42) at offset 0 of
-- the buffer `[0x2a]` from `0x2000` ⇒ `x11 = 0x2a` and `decodeScalar [0x2a] = some (42, [])`.
example :=
  unified_scalar_field_decode (0x1000 : Word) (0x2000 : Word)
    [(0x2a : Byte)] 0 [(0x2a : Byte)] [] 0 0 0 0 0 0
    (by decide) (by decide) (by decide) (by decide)
    (by intro i hi
        have hlen : ([(0x2a : Byte)]).length = 1 := by decide
        rw [hlen] at hi
        interval_cases i
        decide)
    (by decide)

end EvmAsm.Rv64.RLP

