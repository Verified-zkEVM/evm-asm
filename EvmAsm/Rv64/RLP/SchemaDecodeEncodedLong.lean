/-
  EvmAsm.Rv64.RLP.SchemaDecodeEncodedLong

  EL.3 / Phase 5 — long-list end-user decode API. The long-list counterpart of
  `decode_encoded_short_list_schema`: when the input buffer (from `O`) is the genuine RLP
  encoding of the field record as a LONG list (payload `> 55`, the real tx/header case), the
  decoder runs and yields the field-by-field result. The `longList` prefix fact, the
  length-bytes-fit bound, and `SchemaValid` are all derived from the encoding — using the
  `Nat.toBytesBE` length bounds (`1 ≤ lenOfLen ≤ 8`) for the prefix range.
-/

import EvmAsm.Rv64.RLP.SchemaListWalkLong
import EvmAsm.Rv64.RLP.SchemaListEncodeLong

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

set_option maxRecDepth 8000 in
/-- **Decode an RLP-encoded long-list field record.** When the buffer from `O` is the RLP
    long-list encoding of the field items (`encode (.list (schemaItems specs)) ++ tail`) with
    payload `> 55` and `< 256 ^ 8` bytes, the decoder reads each field into the output region;
    the prefix-class fact, length bound, and `SchemaValid` are discharged from the encoding. -/
theorem decode_encoded_long_list_schema
    (base regionBase outBase : Word) (rOut : Reg) (bs : List Byte) (O : Nat) (hO : O < bs.length)
    (specs : List FieldSpec) (out : List Byte) (outLen : Nat) (tail : List Byte)
    (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (hsizeLo : 55 < (schemaEncBytes specs).length)
    (hsizeHi : (schemaEncBytes specs).length < 256 ^ 8)
    (hbs : bs.drop O = encode (.list (schemaItems specs)) ++ tail)
    (hcore : ∀ f, f ∈ specs → fieldCoreValid outLen f)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hlen : out.length = outLen)
    (hdov : outBase.toNat + outLen < 2 ^ 64)
    (hdval : ∀ i, i < outLen → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + (148 + schemaSize specs) < 2 ^ 64) :
    cpsTripleWithin (61 + schemaSteps specs) base
        ((base + 148) + BitVec.ofNat 64 (schemaSize specs))
      (((CodeReq.singleton base (.LBU .x5 .x13 0)).union
          (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
        (schemaCR (base + 148) rOut specs))
      (((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
        (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase out))
      (schemaINV regionBase outBase rOut bs
        (((O + 1) + rlpPrefixLongListLenOfLen (bs[O]'hO)) + schemaEnc specs)
        (schemaOut out specs))
    ∧ schemaDecodes bs ((O + 1) + rlpPrefixLongListLenOfLen (bs[O]'hO)) specs := by
  set lenBytesLen := (Nat.toBytesBE (schemaEncBytes specs).length).length with hLBL
  -- `lenOfLen` is in `[1, 8]`.
  have hk8 : lenBytesLen ≤ 8 := Nat.toBytesBE_length_le _ 8 hsizeHi
  have hk1 : 1 ≤ lenBytesLen := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
      (show (schemaEncBytes specs).length ≠ 0 from by omega)
    rw [hLBL, hm, Nat.toBytesBE_succ, List.length_append]; simp
  -- The buffer byte at `O` is the long-list header `0xF7 + lenOfLen`.
  have hbs_head : bs[O]'hO = (encode (.list (schemaItems specs)))[0]'(encode_nonempty _) := by
    have key : (bs.drop O)[0]'(by rw [List.length_drop]; omega)
        = (encode (.list (schemaItems specs)))[0]'(encode_nonempty _) :=
      (List.getElem_of_eq hbs _).trans (List.getElem_append_left (encode_nonempty _))
    rw [← key]; simp
  have hhead : (encode (.list (schemaItems specs)))[0]'(encode_nonempty _)
      = BitVec.ofNat 8 (0xF7 + lenBytesLen) := by
    have key := List.getElem_of_eq (encode_list_schemaItems_long specs (by omega))
      (encode_nonempty (RLPItem.list (schemaItems specs)))
    rw [key]; rfl
  have hbsO : bs[O]'hO = BitVec.ofNat 8 (0xF7 + lenBytesLen) := hbs_head.trans hhead
  have htoNat : (bs[O]'hO).toNat = 0xF7 + lenBytesLen := by
    rw [hbsO, BitVec.toNat_ofNat]; omega
  -- `rlpPrefixLongListLenOfLen` recovers `lenOfLen`.
  have hk_eq : rlpPrefixLongListLenOfLen (bs[O]'hO) = lenBytesLen := by
    rw [rlpPrefixLongListLenOfLen, htoNat]; omega
  -- The prefix classifies as a long list.
  have hpfx : classifyPrefix (bs[O]'hO) = .longList := by
    rw [classifyPrefix_longList_iff, htoNat]; omega
  -- The length bytes fit in the buffer (the payload follows them).
  have hfit : (O + 1) + rlpPrefixLongListLenOfLen (bs[O]'hO) ≤ bs.length := by
    have hd := schemaConcat_of_encode_list_long bs specs O tail (by omega) hbs
    have := congrArg List.length hd
    rw [List.length_drop, List.length_append] at this
    rw [hk_eq]; omega
  -- `SchemaValid` from the encoding payload.
  have hvalid : SchemaValid bs outLen ((O + 1) + rlpPrefixLongListLenOfLen (bs[O]'hO)) specs := by
    rw [hk_eq]
    refine schemaValid_of_concat bs outLen tail specs ((O + 1) + lenBytesLen) hcore ?_
    rw [show (O + 1) + lenBytesLen = O + (1 + lenBytesLen) from by omega]
    exact schemaConcat_of_encode_list_long bs specs O tail (by omega) hbs
  exact long_list_schema_walk base regionBase outBase rOut bs O hO specs out outLen
    v5Old v10 v11Old v12Old v14Old v15Old hpfx hfit halign hover hwin hdalign hlen hdov hdval
    hvalid hcode

end EvmAsm.Rv64.RLP
