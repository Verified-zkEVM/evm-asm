/-
  EvmAsm.Rv64.RLP.UnifiedScalarFieldZero

  EL.3 / Phase 5 — the EMPTY (`n = 0`) scalar field. In RLP a scalar `0` is the
  empty byte string `[0x80]`, and minimal encoding means EVERY zero-valued scalar
  (`nonce = 0`, `value = 0`, an empty `to`, …) appears on the wire this way. The
  general scalar unit (`unified_scalar_field_decode_and_store`) requires
  `1 ≤ data.length`, so it cannot decode a zero field — the big-endian read loop has
  no zero-trip spec.

  This file closes that gap with a dedicated zero-trip unit. The observation that
  makes it cheap: for an empty `.bytes []` field the single-item header descent
  (`unified_list_header_descend`) already advances `x13` to the payload pointer,
  which — the payload being empty — IS the next field (`regionBase + ofNat (O+1)`).
  So there is nothing to read: just descend, then `SD rOut, x0, offset` to write the
  value `0` (from the always-zero register `x0`). Coincides with the pure
  `decodeScalar (bs.drop O) = some (0, tail)`.

  Layout (program base `base`; aligned `regionBase`, buffer `bs`, field offset `O`;
  output pointer register `rOut`, output base `outBase`, struct slot `offset`):
      base       < LBU + unified_decoder : item header descent >
                 (base .. base+148)                  ; x13 → next field (payload empty)
      base+148   SD rOut, x0, offset                 ; [outBase + offset] := 0
      base+152   (exit)
-/

import EvmAsm.Rv64.RLP.UnifiedScalarFieldDecode
import EvmAsm.Rv64.InstructionSpecs

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

set_option maxRecDepth 8000 in
/-- **Decode-and-store an empty (`n = 0`) scalar field.** From `x13 = regionBase +
    ofNat O` pointing at the empty byte string `[0x80]` (i.e. `bs.drop O = encode
    (.bytes []) ++ tail`), descend the item header — which advances `x13` to the next
    field, the empty payload contributing nothing — and write the scalar value `0` to
    the output cell `outBase + offset` via `SD rOut, x0, offset`. Coincides with the
    pure `decodeScalar (bs.drop O) = some (0, tail)`. -/
theorem unified_scalar_field_decode_and_store_zero
    (base regionBase : Word) (rOut : Reg) (outBase memOld : Word) (offset : BitVec 12)
    (bs : List Byte) (O : Nat) (tail : List Byte)
    (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdrop : bs.drop O = encode (.bytes ([] : List Byte)) ++ tail) :
    cpsTripleWithin 62 base (base + 152)
      (((CodeReq.singleton base (.LBU .x5 .x13 0)).union
          (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
          (CodeReq.singleton (base + 148) (.SD rOut .x0 offset)))
      (((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
        (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** ((outBase + signExtend12 offset) ↦ₘ memOld)))
      (((rOut ↦ᵣ outBase) ** (.x0 ↦ᵣ (0 : Word)) **
        ((outBase + signExtend12 offset) ↦ₘ (0 : Word))) **
       ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes ([] : List Byte))).length))) **
        regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x14 **
        (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs))
    ∧ decodeScalar (bs.drop O) = some (0, tail) := by
  -- `encode (.bytes []) = [0x80]`, length 1.
  have henc_len : (encode (.bytes ([] : List Byte))).length = 1 := by
    simp [encode, encodeBytes_nil]
  -- Offset bookkeeping.
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
  -- The `0x80` prefix classifies as `.shortBytes`; its payload pointer is `O + 1`.
  have hhead80 : bs[O]'hbs0 = (BitVec.ofNat 8 0x80 : Byte) := by
    rw [hbs_head]; simp [encode, encodeBytes_nil]
  have hcls : classifyPrefix (bs[O]'hbs0) = .shortBytes := by rw [hhead80]; decide
  have hptr : itemPtrRegion (bs[O]'hbs0) regionBase O
      = regionBase + BitVec.ofNat 64 (O + (encode (.bytes ([] : List Byte))).length) := by
    simp only [itemPtrRegion, hcls]; rw [henc_len]
  -- Window facts for the descent (same construction as `unified_scalar_field_decode`).
  have hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 O) = true := hwin O hbs0
  have hwindow0 : regionLongWindow regionBase bs O hbs0 :=
    regionLongWindow_of_split regionBase bs (.bytes ([] : List Byte)) tail O hbs0 hbs_head hdrop
      (by simp [itemPayloadCount]) hwin
  -- t_desc : the item-header descent, with `x13` rewritten to the next field, and the
  -- clobbered scratch (x5,x10,x11,x12,x14) weakened to the canonical `regOwn` interface.
  have t_desc := unified_list_header_descend base regionBase bs O hbs0
    v5Old v10 v11Old v12Old v14Old v15Old halign hover hvalid0 hwindow0
  rw [hptr] at t_desc
  have t_desc_r := cpsTripleWithin_weaken (fun _ h => h)
    (fun _ hp =>
      sepConj_mono (regIs_implies_regOwn .x5)
        (sepConj_mono_right
          (sepConj_mono (regIs_implies_regOwn .x10)
            (sepConj_mono (regIs_implies_regOwn .x11)
              (sepConj_mono (regIs_implies_regOwn .x12)
                (sepConj_mono_right
                  (sepConj_mono (regIs_implies_regOwn .x14) (fun _ x => x))))))) _ hp)
    t_desc
  -- Frame the output pointer and cell alongside the descent.
  have t_desc_f := cpsTripleWithin_frameR
    ((rOut ↦ᵣ outBase) ** ((outBase + signExtend12 offset) ↦ₘ memOld)) (by pcFree) t_desc_r
  -- The store: SD rOut, x0, offset (writes the 0 held in x0).
  have s_sd := sd_spec_within rOut .x0 outBase (0 : Word) memOld offset (base + 148)
  -- Frame the rest of the state (everything except rOut/x0/cell) around the store.
  have s_store := cpsTripleWithin_frameR
    ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes ([] : List Byte))).length))) **
     regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x14 **
     (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs)
    (by pcFree) s_sd
  rw [show base + 148 + 4 = base + 152 from by bv_omega] at s_store
  -- Disjointness: the descent CR (base .. base+148) ⊥ the store at base+148.
  have hd : ((CodeReq.singleton base (.LBU .x5 .x13 0)).union
        (CodeReq.ofProg (base + 4) unified_decoder_prog)).Disjoint
      (CodeReq.singleton (base + 148) (.SD rOut .x0 offset)) :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.ofProg_singleton
        (CodeReq.ofProg_none_range_len (base + 4) unified_decoder_prog 36 (base + 148)
          unified_decoder_prog_length (by intro k hk; bv_omega)))
  refine ⟨?_, ?_⟩
  · have composed := cpsTripleWithin_seq hd
      (cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp) t_desc_f)
      s_store
    rw [show 61 + 1 = 62 from by ring] at composed
    exact composed
  · rw [hdrop]
    unfold decodeScalar
    rw [decode_encode_append (.bytes ([] : List Byte)) tail (by rw [henc_len]; norm_num)]
    simp [Nat.fromBytesBE_nil]

-- Concrete cross-check: decode the empty scalar `[0x80]` at offset 0 of the buffer
-- `[0x80]` from `0x2000`, storing the value `0` to `0x3000` via `x18` ⇒ the output
-- cell `0x3000 ↦ₘ 0` and `decodeScalar [0x80] = some (0, [])`.
example :=
  unified_scalar_field_decode_and_store_zero (0x1000 : Word) (0x2000 : Word) .x18
    (0x3000 : Word) 0 0 [(0x80 : Byte)] 0 [] 0 0 0 0 0 0
    (by decide) (by decide)
    (by intro i hi
        have hlen : ([(0x80 : Byte)]).length = 1 := by decide
        rw [hlen] at hi
        interval_cases i
        decide)
    (by decide)

end EvmAsm.Rv64.RLP
