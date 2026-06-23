/-
  EvmAsm.Rv64.RLP.SchemaDecodeValues

  EL.3 / Phase 5 — end-user decode-to-FIELD-VALUES API. The `decode_encoded_{short,long}_list_schema`
  theorems take RLP-encoded list bytes and yield the operational decode triple plus the per-field
  `schemaDecodes` coincidence (each field decodes as a scalar or a byte array). A real STF consumer
  wants the numeric VALUE of every field uniformly — and (per `UnifiedWideScalarField`) a transaction's
  `u256` fields ride the byte-array path, so the fold reports them via `decode`/`.bytes`.

  This file packages the final step: combine the encoded-list decoders with
  `schemaDecodes_imp_scalarValues` (`SchemaScalarValues`) so the conclusion is `schemaScalarValues` —
  every field's big-endian value at its input offset. The result is the one-shot API behind the
  concrete tx/header decoders: RLP bytes in → operational decode + all field values out, verified.
-/

import EvmAsm.Rv64.RLP.SchemaDecodeEncoded
import EvmAsm.Rv64.RLP.SchemaDecodeEncodedLong
import EvmAsm.Rv64.RLP.SchemaScalarValues

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

set_option maxRecDepth 8000 in
/-- **Decode a short-list field record to field VALUES.** As `decode_encoded_short_list_schema` but
    the conclusion additionally yields `schemaScalarValues` — every field's big-endian value at its
    input offset (`O + 1`), whether decoded as a scalar or a byte array. -/
theorem decode_encoded_short_list_schema_values
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
    ∧ schemaScalarValues bs (O + 1) specs := by
  obtain ⟨htrip, hdec⟩ := decode_encoded_short_list_schema base regionBase outBase rOut bs O specs
    out outLen tail v5Old v10 v11Old v12Old v14Old v15Old hsize hbs hcore halign hover hwin hdalign
    hlen hdov hdval hcode
  exact ⟨htrip, schemaDecodes_imp_scalarValues bs (O + 1) specs hdec⟩

set_option maxRecDepth 8000 in
/-- **Decode a long-list field record to field VALUES.** As `decode_encoded_long_list_schema` but
    the conclusion additionally yields `schemaScalarValues` — every field's big-endian value at its
    input offset (`(O + 1) + lenOfLen`). The real tx/header case (payload `> 55`). -/
theorem decode_encoded_long_list_schema_values
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
    ∧ schemaScalarValues bs ((O + 1) + rlpPrefixLongListLenOfLen (bs[O]'hO)) specs := by
  obtain ⟨htrip, hdec⟩ := decode_encoded_long_list_schema base regionBase outBase rOut bs O hO specs
    out outLen tail v5Old v10 v11Old v12Old v14Old v15Old hsizeLo hsizeHi hbs hcore halign hover hwin
    hdalign hlen hdov hdval hcode
  exact ⟨htrip, schemaDecodes_imp_scalarValues bs ((O + 1) + rlpPrefixLongListLenOfLen (bs[O]'hO))
    specs hdec⟩

end EvmAsm.Rv64.RLP
