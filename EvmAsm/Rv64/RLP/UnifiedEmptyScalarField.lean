/-
  EvmAsm.Rv64.RLP.UnifiedEmptyScalarField

  EL.3 / Phase 5 — the EMPTY (`n=0`) scalar field, storing into the output REGION. A zero scalar
  (`nonce=0`, `value=0`, `v=0`) RLP-encodes as the empty string `[0x80]`; the non-empty scalar
  region unit (`unified_scalar_field_decode_and_store_region`) requires `1 ≤ data.length` (its
  big-endian read loop has no zero-trip spec), so it cannot decode a zero field into the schema
  engine's shared output `bytesRegion`.

  This is the region analog of the merged cell-based `unified_scalar_field_decode_and_store_zero`:
  the single-item header descent on `0x80` already leaves `x13` at the next field (empty payload)
  and `x11 = itemLenRegion = 0`, so there is nothing to read — descend, then spill the value `0`
  (held in `x11`) into the output region at byte offset `di0` via the scalar store-region leaf
  (`spillRange out 0 di 8`). Coincides with `decodeScalar (bs.drop O) = some (0, tail)`.

  Machine: descend (`base .. base+148`) ⨾ `ADDI x14,rOut,imm` + 8-iteration spill chain
  (`base+148 .. base+148+4+ofNat(12·8)`) — `fieldSize = 248`, 32 bytes shorter than the non-empty
  scalar unit (no read loop).
-/

import EvmAsm.Rv64.RLP.UnifiedScalarFieldRegion
import EvmAsm.Rv64.RLP.UnifiedScalarFieldDecode

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

set_option maxRecDepth 8000 in
/-- **Empty (`n=0`) scalar field decode-and-store into region.** From `x13 = regionBase + ofNat O`
    pointing at the empty byte string `[0x80]`, descend the header (advancing `x13` to the next
    field, the empty payload contributing nothing) and spill the scalar value `0` into the output
    region at byte offset `di0` (`spillRange out 0 di0 8`). Coincides with
    `decodeScalar (bs.drop O) = some (0, tail)`. -/
theorem unified_empty_scalar_field_decode_and_store_region
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (tail : List Byte) (outBytes : List Byte) (di0 : Nat)
    (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdrop : bs.drop O = encode (.bytes ([] : List Byte)) ++ tail)
    (hdalign : outBase.toNat % 8 = 0) (hdst : di0 + 8 ≤ outBytes.length)
    (hdov : outBase.toNat + outBytes.length < 2 ^ 64)
    (hdval : ∀ i, i < outBytes.length → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hImm : signExtend12 fieldImm = BitVec.ofNat 64 di0)
    (hcode : base.toNat + (148 + 4 + 12 * 8) < 2 ^ 64) :
    cpsTripleWithin (61 + (1 + 3 * 8)) base (base + 148 + 4 + BitVec.ofNat 64 (12 * 8))
      (((CodeReq.singleton base (.LBU .x5 .x13 0)).union
          (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
        ((CodeReq.singleton (base + 148) (.ADDI .x14 rOut fieldImm)).union
          (spillChainCR (base + 148 + 4) 8)))
      (((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
        (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      (((regOwn .x11) ** (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + 8))) ** (rOut ↦ᵣ outBase) **
        bytesRegion outBase
          (spillRange outBytes (BitVec.ofNat 64 (Nat.fromBytesBE ([] : List Byte))) di0 8)) **
       ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes ([] : List Byte))).length))) **
        regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
        regOwn .x5 ** regOwn .x10 ** (.x15 ↦ᵣ v15Old)))
    ∧ decodeScalar (bs.drop O) = some (0, tail) := by
  -- `encode (.bytes []) = [0x80]`, length 1.
  have henc_len : (encode (.bytes ([] : List Byte))).length = 1 := by
    simp [encode, encodeBytes_nil]
  have hbs0 : O < bs.length := by
    have h := congrArg List.length hdrop
    rw [List.length_drop, List.length_append] at h
    have := encode_nonempty (RLPItem.bytes ([] : List Byte)); omega
  have hbs_head : bs[O]'hbs0
      = (encode (.bytes ([] : List Byte)))[0]'(encode_nonempty (RLPItem.bytes ([] : List Byte))) := by
    have key : (bs.drop O)[0]'(by rw [List.length_drop]; omega)
        = (encode (.bytes ([] : List Byte)))[0]'(encode_nonempty (RLPItem.bytes ([] : List Byte))) :=
      (List.getElem_of_eq hdrop _).trans (List.getElem_append_left (encode_nonempty _))
    rw [← key]; simp
  have hhead80 : bs[O]'hbs0 = (BitVec.ofNat 8 0x80 : Byte) := by
    rw [hbs_head]; simp [encode, encodeBytes_nil]
  have hcls : classifyPrefix (bs[O]'hbs0) = .shortBytes := by rw [hhead80]; decide
  have hptr : itemPtrRegion (bs[O]'hbs0) regionBase O
      = regionBase + BitVec.ofNat 64 (O + (encode (.bytes ([] : List Byte))).length) := by
    simp only [itemPtrRegion, hcls]; rw [henc_len]
  have hlenval : itemLenRegion (bs[O]'hbs0) bs O
      = BitVec.ofNat 64 (Nat.fromBytesBE ([] : List Byte)) := by
    simp only [itemLenRegion, hcls]
    rw [hhead80]
    decide
  have hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 O) = true := hwin O hbs0
  have hwindow0 : regionLongWindow regionBase bs O hbs0 :=
    regionLongWindow_of_split regionBase bs (.bytes ([] : List Byte)) tail O hbs0 hbs_head hdrop
      (by simp [itemPayloadCount]) hwin
  -- Descend the item header; rewrite `x13`/`x11` to the next-field pointer and the value `0`, then
  -- weaken the clobbered scratch (x5, x10, x12) to `regOwn` (the store leaves them owned).
  have t_desc := unified_list_header_descend base regionBase bs O hbs0
    v5Old v10 v11Old v12Old v14Old v15Old halign hover hvalid0 hwindow0
  rw [hptr, hlenval] at t_desc
  have t_desc_r := cpsTripleWithin_weaken (fun _ h => h)
    (fun _ hp =>
      sepConj_mono (regIs_implies_regOwn .x5)
        (sepConj_mono_right
          (sepConj_mono (regIs_implies_regOwn .x10)
            (sepConj_mono_right
              (sepConj_mono (regIs_implies_regOwn .x12) (fun _ x => x))))) _ hp)
    t_desc
  -- Frame the output region + pointer through the descend.
  have t_desc' := cpsTripleWithin_frameR ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes)
    (by exact pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _)) t_desc_r
  -- The scalar store-region leaf at base+148, spilling the value `0` (held in x11).
  have store := unified_field_scalar_store_region (base + 148) rOut outBase fieldImm outBytes di0 8
    (BitVec.ofNat 64 (Nat.fromBytesBE ([] : List Byte))) (itemX14 (bs[O]'hbs0) v14Old)
    hdalign hdst hdov hdval
    (by have h148 : (base + 148).toNat = base.toNat + 148 := by bv_omega
        omega) hImm
  -- Frame the descend-leftover registers / input region through the store.
  have store' := cpsTripleWithin_frameR
    ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes ([] : List Byte))).length))) **
     regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
     regOwn .x5 ** regOwn .x10 ** (.x15 ↦ᵣ v15Old))
    (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regOwn (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj (bytesRegion_pcFree _ _) (pcFree_sepConj pcFree_regOwn
        (pcFree_sepConj pcFree_regOwn pcFree_regIs)))))) store
  -- Disjointness: descend CR ⊥ store CR.
  have hd : ((CodeReq.singleton base (.LBU .x5 .x13 0)).union
        (CodeReq.ofProg (base + 4) unified_decoder_prog)).Disjoint
      ((CodeReq.singleton (base + 148) (.ADDI .x14 rOut fieldImm)).union
        (spillChainCR (base + 148 + 4) 8)) := by
    refine CodeReq.Disjoint.union_left ?_ ?_ <;>
      · refine CodeReq.Disjoint.union_right ?_ ?_
        · first
            | exact CodeReq.Disjoint.singleton (by bv_omega)
            | exact CodeReq.Disjoint.ofProg_singleton
                (CodeReq.ofProg_none_range_len _ _ 36 _ unified_decoder_prog_length
                  (by intro k hk; bv_omega))
        · intro a'
          by_cases hh : ∀ j, j < 3 * 8 → a' ≠ (base + 148 + 4) + BitVec.ofNat 64 (4 * j)
          · exact Or.inr (spillChainCR_none (base + 148 + 4) a' 8 hh)
          · push Not at hh; obtain ⟨j, hj, rfl⟩ := hh
            first
              | exact Or.inl (CodeReq.singleton_miss (by bv_omega))
              | exact Or.inl (CodeReq.ofProg_none_range_len _ _ 36 _ unified_decoder_prog_length
                  (by intro k hk; bv_omega))
  refine ⟨?_, ?_⟩
  · exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_seq hd
        (cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp) t_desc')
        store')
  · rw [hdrop]
    unfold decodeScalar
    rw [decode_encode_append (.bytes ([] : List Byte)) tail (by rw [henc_len]; norm_num)]
    simp [Nat.fromBytesBE_nil]

end EvmAsm.Rv64.RLP
