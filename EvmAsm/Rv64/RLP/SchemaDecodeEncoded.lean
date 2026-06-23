/-
  EvmAsm.Rv64.RLP.SchemaDecodeEncoded

  EL.3 / Phase 5 — the end-user decode API. Given that the input buffer (from offset `O`) is the
  genuine RLP encoding of the field record — `encode (.list (schemaItems specs)) ++ tail`, with a
  short-list-sized payload — this runs the whole decoder and yields the field-by-field result,
  deriving BOTH the prefix-class fact and `SchemaValid` from the encoding (via the encode bridge
  and `schemaValid_of_concat`). The caller supplies only the encoding fact, per-field core
  validity, and the region/output well-formedness — no RLP-internal proof obligations.
-/

import EvmAsm.Rv64.RLP.SchemaListWalkShort
import EvmAsm.Rv64.RLP.SchemaListEncode

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

set_option maxRecDepth 8000 in
/-- **Decode an RLP-encoded short-list field record.** When the buffer from `O` is the RLP
    encoding of the field items (`encode (.list (schemaItems specs)) ++ tail`) with payload
    `≤ 55` bytes, the decoder reads each field into the shared output region; the prefix-class
    fact and `SchemaValid` are discharged from the encoding. -/
theorem decode_encoded_short_list_schema
    (base regionBase outBase : Word) (rOut : Reg) (bs : List Byte) (O : Nat)
    (specs : List FieldSpec) (out : List Byte) (outLen : Nat) (tail : List Byte)
    (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (hsize : (schemaEncBytes specs).length ≤ 55)
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
      (schemaINV regionBase outBase rOut bs ((O + 1) + schemaEnc specs) (schemaOut out specs))
    ∧ schemaDecodes bs (O + 1) specs := by
  -- The list encoding is non-empty, so `O` is in range.
  have hbs0 : O < bs.length := by
    have h := congrArg List.length hbs
    rw [List.length_drop, List.length_append] at h
    have := encode_nonempty (RLPItem.list (schemaItems specs))
    omega
  -- The buffer byte at `O` is the list header `0xC0 + payloadLen`.
  have hbs_head : bs[O]'hbs0
      = (encode (.list (schemaItems specs)))[0]'(encode_nonempty _) := by
    have key : (bs.drop O)[0]'(by rw [List.length_drop]; omega)
        = (encode (.list (schemaItems specs)))[0]'(encode_nonempty _) :=
      (List.getElem_of_eq hbs _).trans (List.getElem_append_left (encode_nonempty _))
    rw [← key]; simp
  have hhead : (encode (.list (schemaItems specs)))[0]'(encode_nonempty _)
      = BitVec.ofNat 8 (0xC0 + (schemaEncBytes specs).length) := by
    have key := List.getElem_of_eq (encode_list_schemaItems_short specs hsize)
      (encode_nonempty (RLPItem.list (schemaItems specs)))
    rw [key]; rfl
  -- Hence the prefix classifies as a short list.
  have hpfx : classifyPrefix (bs[O]'hbs0) = .shortList := by
    rw [hbs_head, hhead, classifyPrefix_shortList_iff, BitVec.toNat_ofNat]
    omega
  -- `SchemaValid` from the encoding: the payload is exactly `schemaEncBytes`.
  have hvalid : SchemaValid bs outLen (O + 1) specs :=
    schemaValid_of_concat bs outLen tail specs (O + 1) hcore
      (schemaConcat_of_encode_list_short bs specs O tail hsize hbs)
  exact short_list_schema_walk base regionBase outBase rOut bs O hbs0 specs out outLen
    v5Old v10 v11Old v12Old v14Old v15Old hpfx halign hover hwin hdalign hlen hdov hdval hvalid hcode

end EvmAsm.Rv64.RLP
