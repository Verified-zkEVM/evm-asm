/-
  EvmAsm.Rv64.RLP.UnifiedLongBytesField

  EL.3 / Phase 5 — LONG byte-array field decode-and-copy (`data.length > 55`). The
  short byte-array unit (`unified_bytes_field_decode_and_copy`) caps at `≤ 55` bytes
  (RLP short-string form). Real structures need more: a transaction's `data` (contract
  calldata) is routinely `> 55` bytes, and a block header's `logsBloom` is a fixed
  256-byte field — both RLP long-string form (`0xB8..0xBF`: prefix `0xB7 + lenOfLen`,
  then `lenOfLen` big-endian length bytes, then the payload).

  The single-item decoder already handles long byte strings (`itemPtrRegion` /
  `itemLenRegion` have `longBytes` branches reading the length bytes from the region),
  and the byte-copy leaf (`unified_field_bytes_copy`) is length-generic, so the only
  new ingredient is the LONG payload-window lemma (`bytes_item_payload_window_long`):
  for a long `.bytes data` item the payload pointer is `regionBase + ofNat(off + 1 +
  lenOfLen)`, the recovered length is `data.length`, and the region from there is
  `data ++ tail`. Composing descent ⨾ copy then mirrors the short unit.

  (No concrete `example`: `Nat.toBytesBE` is well-founded recursive and does not reduce
  under `decide`, so a long-form encoding cannot be discharged by computation — the same
  reason the codebase's long-list cross-checks go through the abstract theorems.)
-/

import EvmAsm.Rv64.RLP.UnifiedBytesFieldDecode
import EvmAsm.Rv64.RLP.LongItemStride

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

/-- **Long `.bytes`-item payload window.** The `longBytes` analog of
    `bytes_item_payload_window`: for a long `.bytes data` item (`data.length > 55`) at
    byte offset `off`, the decoder's payload pointer skips the prefix byte and the
    `lenOfLen` length bytes, the recovered length is `data.length`, and the region from
    the payload offset is exactly `data ++ tail`. -/
theorem bytes_item_payload_window_long (data tail : List Byte)
    (regionBase : Word) (off : Nat) (bs : List Byte)
    (hdrop : bs.drop off = encode (.bytes data) ++ tail)
    (hlong : 55 < data.length) (hsize : data.length < 256 ^ 8) :
    itemPtrRegion ((encode (.bytes data))[0]'(encode_nonempty _)) regionBase off
        = regionBase + BitVec.ofNat 64 (off + 1 + itemLenOfLen (.bytes data))
      ∧ itemLenRegion ((encode (.bytes data))[0]'(encode_nonempty _)) bs off
        = BitVec.ofNat 64 data.length
      ∧ bs.drop (off + 1 + itemLenOfLen (.bytes data)) = data ++ tail := by
  have hisLong : isLongItem (.bytes data) := by simpa [isLongItem] using hlong
  have hk8 : (Nat.toBytesBE data.length).length ≤ 8 := Nat.toBytesBE_length_le data.length 8 hsize
  have hbound : 0xB7 + (Nat.toBytesBE data.length).length < 256 :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_left hk8 0xB7) (by norm_num)
  have hlol : itemLenOfLen (.bytes data) = (Nat.toBytesBE data.length).length := by
    simp only [itemLenOfLen, itemPayloadCount]
  have henc : encode (.bytes data)
      = [BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length)]
          ++ Nat.toBytesBE data.length ++ data :=
    encodeBytes_long_of_length data hlong
  have hhead : (encode (.bytes data))[0]'(encode_nonempty _)
      = BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length) := by simp [henc]
  have htn : (BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length)).toNat
      = 0xB7 + (Nat.toBytesBE data.length).length := by
    rw [BitVec.toNat_ofNat, show (2:Nat)^8 = 256 from rfl, Nat.mod_eq_of_lt hbound]
  have hcls : classifyPrefix ((encode (.bytes data))[0]'(encode_nonempty _)) = .longBytes := by
    rcases classifyPrefix_encode_head_long (.bytes data) hisLong
        (by simpa [itemPayloadCount] using hsize) with h | h
    · exact h
    · exfalso
      rw [hhead, classifyPrefix_longList_iff, htn] at h
      exact absurd h (Nat.not_le.mpr
        (Nat.lt_of_le_of_lt (Nat.add_le_add_left hk8 0xB7) (by norm_num)))
  have hlenoflen : rlpPrefixLongBytesLenOfLen ((encode (.bytes data))[0]'(encode_nonempty _))
      = (Nat.toBytesBE data.length).length := by
    rw [← hlol]; exact encode_long_lenOfLen_eq_bytes hlong hsize
  -- The region from `off + 1` is `toBytesBE len ++ (data ++ tail)`.
  have hdrop1 : bs.drop (off + 1) = Nat.toBytesBE data.length ++ (data ++ tail) := by
    have hd1 : bs.drop (off + 1) = (bs.drop off).drop 1 := by rw [List.drop_drop]
    rw [hd1, hdrop, henc]
    simp [List.append_assoc]
  refine ⟨?_, ?_, ?_⟩
  · simp only [itemPtrRegion, hcls, hlenoflen]
    rw [show (off + 1) + (Nat.toBytesBE data.length).length
          = off + 1 + itemLenOfLen (.bytes data) from by rw [hlol]]
  · simp only [itemLenRegion, hcls, hlenoflen, hdrop1]
    rw [List.take_left' rfl, Nat.fromBytesBE_toBytesBE]
  · rw [hlol, ← List.drop_drop, hdrop1, List.drop_left' rfl]

set_option maxRecDepth 8000 in
/-- **Long byte-array field decode-and-copy.** Decode the long `.bytes data` field
    (`data.length > 55`) at `x13 = regionBase + ofNat O` and copy its payload into the
    output region at byte offset `di0`. Same machine shape as the short byte-array unit
    (the single-item decoder handles the long header natively); coincides with
    `decode (bs.drop O) = some (.bytes data, tail)`. Covers calldata and the 256-byte
    `logsBloom`. -/
theorem unified_long_bytes_field_decode_and_copy
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (data tail : List Byte) (outBytes : List Byte) (di0 : Nat)
    (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (hlong : 55 < data.length)
    (hsize : (encode (.bytes data)).length < 256 ^ 8)
    (halign : regionBase.toNat % 8 = 0) (hdalign : outBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hImm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (hdst : di0 + data.length ≤ outBytes.length)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + (148 + 4 + 20 * data.length) < 2 ^ 64)
    (hdrop : bs.drop O = encode (.bytes data) ++ tail) :
    cpsTripleWithin (61 + (1 + 5 * data.length)) base (base + 148 + 4 + BitVec.ofNat 64 (20 * data.length))
      (((CodeReq.singleton base (.LBU .x5 .x13 0)).union
          (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
        ((CodeReq.singleton (base + 148) (.ADDI .x14 rOut fieldImm)).union
          (byteCopyChainCR (base + 148 + 4) data.length)))
      (((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
        (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      (((regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes data)).length))) **
        (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + data.length))) ** (regOwn .x15) **
        (rOut ↦ᵣ outBase) ** bytesRegion regionBase bs **
        bytesRegion outBase (copyRangeGen outBytes data 0 di0 data.length)) **
       (regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 ** regOwn .x11))
    ∧ decode (bs.drop O) = some (.bytes data, tail) := by
  -- `data.length < 256^8` (payload count) and `O < bs.length`.
  have hisLong : isLongItem (.bytes data) := by simpa [isLongItem] using hlong
  have hdle : data.length ≤ (encode (.bytes data)).length := by
    rw [encode_long_length_eq (.bytes data) hisLong]; simp only [itemPayloadCount]; omega
  have hsizeData : data.length < 256 ^ 8 := lt_of_le_of_lt hdle hsize
  have hbs0 : O < bs.length := by
    have h := congrArg List.length hdrop
    rw [List.length_drop, List.length_append] at h
    have := encode_nonempty (RLPItem.bytes data); omega
  have hbs_head : bs[O]'hbs0 = (encode (.bytes data))[0]'(encode_nonempty (RLPItem.bytes data)) := by
    have key : (bs.drop O)[0]'(by rw [List.length_drop]; omega)
        = (encode (.bytes data))[0]'(encode_nonempty (RLPItem.bytes data)) :=
      (List.getElem_of_eq hdrop _).trans (List.getElem_append_left (encode_nonempty _))
    rw [← key]; simp
  obtain ⟨hptr, hlen, hpay⟩ :=
    bytes_item_payload_window_long data tail regionBase O bs hdrop hlong hsizeData
  rw [show ((encode (.bytes data))[0]'(encode_nonempty (RLPItem.bytes data)))
        = (bs[O]'hbs0) from hbs_head.symm] at hptr hlen
  -- Payload offset and its facts (mirrors the short unit).
  set payloadOff := O + 1 + itemLenOfLen (.bytes data) with hpoff_def
  have hpaylen : payloadOff + data.length ≤ bs.length := by
    have e1 := congrArg List.length hpay
    rw [List.length_drop, List.length_append] at e1; omega
  have hstride : payloadOff + data.length = O + (encode (.bytes data)).length := by
    rw [hpoff_def, encode_long_length_eq (.bytes data) hisLong]
    simp only [itemPayloadCount]; omega
  have hwindow0 : regionLongWindow regionBase bs O hbs0 :=
    regionLongWindow_of_split regionBase bs (.bytes data) tail O hbs0 hbs_head hdrop
      (by simpa [itemPayloadCount] using hsizeData) hwin
  -- Header decode (base .. base+148): x13 = payload pointer, x11 = length.
  have hdesc := unified_list_header_descend base regionBase bs O hbs0 v5Old v10 v11Old v12Old
    v14Old v15Old halign hover (hwin O hbs0) hwindow0
  rw [hptr] at hdesc
  -- Frame the output region + pointer through the header descend.
  have hdesc' := cpsTripleWithin_frameR ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes)
    (by exact pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)) hdesc
  -- The leaf byte-array copy (base+148 ..): copies data.length payload bytes to di0.
  have hcopy := unified_field_bytes_copy (base + 148) regionBase rOut outBase fieldImm bs outBytes
    payloadOff di0 data.length (itemX12Region (bs[O]'hbs0) bs O v12Old) (itemX14 (bs[O]'hbs0) v14Old)
    v15Old halign hdalign hover hwin hpaylen hdst hdov hdval
    (by have h148 : (base + 148).toNat = base.toNat + 148 := by bv_omega
        omega) hImm
  -- Frame the header-leftover registers (x5/x0/x10/x11) through the copy.
  have hcopy' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (bs[O]'hbs0).zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x10 ↦ᵣ itemResidue (bs[O]'hbs0)) ** (.x11 ↦ᵣ itemLenRegion (bs[O]'hbs0) bs O))
    (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs pcFree_regIs))) hcopy
  -- Disjointness: header CR ⊥ copy CR (identical to the short unit).
  have hd : ((CodeReq.singleton base (.LBU .x5 .x13 0)).union
        (CodeReq.ofProg (base + 4) unified_decoder_prog)).Disjoint
      ((CodeReq.singleton (base + 148) (.ADDI .x14 rOut fieldImm)).union
        (byteCopyChainCR (base + 148 + 4) data.length)) := by
    refine CodeReq.Disjoint.union_left ?_ ?_
    · refine CodeReq.Disjoint.union_right (CodeReq.Disjoint.singleton (by bv_omega)) ?_
      exact singleton_disjoint_byteCopyChainCR base (base + 148 + 4) _ data.length
        (by have : (base + 148 + 4).toNat = base.toNat + 152 := by bv_omega
            omega)
        (by have : (base + 148 + 4).toNat = base.toNat + 152 := by bv_omega
            omega)
    · refine CodeReq.Disjoint.union_right ?_ ?_
      · exact CodeReq.Disjoint.ofProg_singleton
          (CodeReq.ofProg_none_range_len (base + 4) unified_decoder_prog 36 (base + 148)
            unified_decoder_prog_length (by intro k hk; bv_omega))
      · intro a
        by_cases hdec : ∀ k, k < 36 → a ≠ (base + 4) + BitVec.ofNat 64 (4 * k)
        · exact Or.inl (CodeReq.ofProg_none_range_len (base + 4) unified_decoder_prog 36 a
            unified_decoder_prog_length hdec)
        · push Not at hdec
          obtain ⟨k, hk, rfl⟩ := hdec
          exact Or.inr (byteCopyChainCR_none (base + 148 + 4) _ data.length
            (fun j hj => by bv_omega))
  -- The pure decode coincidence.
  have hpure : decode (bs.drop O) = some (.bytes data, tail) := by
    rw [hdrop]; exact decode_encode_append (.bytes data) tail hsize
  refine ⟨?_, hpure⟩
  -- copyRangeGen over `bs` at payloadOff equals over `data` at 0 (windows agree via hpay).
  have hcongr : copyRangeGen outBytes bs payloadOff di0 data.length
      = copyRangeGen outBytes data 0 di0 data.length := by
    apply copyRangeGen_congr
    intro k hk
    have hk' : payloadOff + k < bs.length := by omega
    have hdk : bs[payloadOff + k]'hk' = data[k]'hk := by
      have h1 := List.getElem_of_eq hpay (i := k) (by rw [List.length_drop]; omega)
      rw [List.getElem_drop] at h1
      rw [h1, List.getElem_append_left hk]
    unfold getByteAt
    rw [dif_pos hk', show (0 + k) = k from Nat.zero_add k, dif_pos hk, hdk]
  rw [hcongr] at hcopy'
  -- Weaken the header-leftover regs to `regOwn` in the copy's framed post.
  have hF2 : ∀ hh, ((.x5 ↦ᵣ (bs[O]'hbs0).zeroExtend 64) ** (.x0 ↦ᵣ (0:Word)) **
        (.x10 ↦ᵣ itemResidue (bs[O]'hbs0)) ** (.x11 ↦ᵣ itemLenRegion (bs[O]'hbs0) bs O)) hh →
      (regOwn .x5 ** (.x0 ↦ᵣ (0:Word)) ** regOwn .x10 ** regOwn .x11) hh :=
    fun hh hf =>
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (regIs_implies_regOwn .x11)))) hh
        ((sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x10)))) hh
          ((sepConj_mono_left (regIs_implies_regOwn .x5)) hh hf))
  have hcopy'' := cpsTripleWithin_weaken (fun _ h => h)
    (fun _ hp => sepConj_mono_right hF2 _ hp) hcopy'
  -- Compose: header descend ⨾ copy, reconciling the framed intermediate state.
  rw [show O + (encode (.bytes data)).length = payloadOff + data.length from hstride.symm]
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq hd
      (cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp) hdesc')
      hcopy'')

end EvmAsm.Rv64.RLP
