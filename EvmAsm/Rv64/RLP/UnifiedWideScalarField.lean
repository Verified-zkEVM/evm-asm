/-
  EvmAsm.Rv64.RLP.UnifiedWideScalarField

  EL.3 / Phase 5 — the WIDE (`u256`) scalar field. The single-word scalar unit
  (`unified_scalar_field_decode_and_store`) reads the payload big-endian into one
  64-bit register, so it caps at `data.length ≤ 8`. But a legacy transaction's
  `nonce, gas_price, gas, value, v, r, s` are `u256` — `r`/`s` are essentially
  always the full 32 bytes — which that unit cannot decode.

  The fix needs no multi-limb big-endian arithmetic. A `u256` scalar's payload is
  ≤ 32 bytes, so it fits the byte-array copy unit
  (`unified_bytes_field_decode_and_copy`, proven for `≤ 55` bytes): copy the raw
  big-endian payload into the output region (contiguous, advancing the output
  cursor `x14`), exactly as the schema fold lays fields out. The scalar VALUE
  coincidence is then free: `decodeScalar` is defined as "decode the item, read its
  bytes as a big-endian natural" with no minimality check, so from the copy unit's
  `decode (bs.drop O) = some (.bytes data, tail)` we get
  `decodeScalar (bs.drop O) = some (Nat.fromBytesBE data, tail)` directly.

  This lifts the scalar field ceiling from 8 to 32 bytes. The output holds the
  field's minimal big-endian bytes (`data.length` of them); fixed-width 32-byte
  zero-padding, if a target struct wants it, is a presentation step layered on at
  schema-assembly time.
-/

import EvmAsm.Rv64.RLP.UnifiedBytesFieldDecode

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

set_option maxRecDepth 8000 in
/-- **Wide (`u256`) scalar field decode-and-copy.** Decode the `.bytes data` scalar
    field at `x13 = regionBase + ofNat O` (`1 ≤ data.length ≤ 32`) and copy its
    `data.length` big-endian payload bytes into the output region at byte offset
    `di0`, advancing the output cursor `x14`. Same machine behaviour as the byte-array
    copy unit; additionally coincides with the pure SCALAR spec
    `decodeScalar (bs.drop O) = some (Nat.fromBytesBE data, tail)` — the field's
    big-endian value. No `data.length ≤ 8` ceiling and no multi-word arithmetic. -/
theorem unified_wide_scalar_field_decode_and_copy
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (data tail : List Byte) (outBytes : List Byte) (di0 : Nat)
    (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (hlen1 : 1 ≤ data.length) (hlen32 : data.length ≤ 32)
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
    ∧ decodeScalar (bs.drop O) = some (Nat.fromBytesBE data, tail) := by
  obtain ⟨htrip, _hdec⟩ := unified_bytes_field_decode_and_copy base regionBase rOut outBase fieldImm
    bs O data tail outBytes di0 v5Old v10 v11Old v12Old v14Old v15Old hlen1 (by omega) hsize
    halign hdalign hover hwin hImm hdst hdov hdval hcode hdrop
  refine ⟨htrip, ?_⟩
  rw [hdrop]
  unfold decodeScalar
  rw [decode_encode_append (.bytes data) tail hsize]
  rfl

-- Concrete cross-check: a 9-byte big-endian payload — the smallest width the old
-- single-word (`≤ 8`) scalar unit could NOT decode. The `.bytes` field at offset 0 of
-- `[0x89, 0x01..0x09]` decodes and copies into a 9-byte output region, with scalar
-- value `Nat.fromBytesBE [0x01,…,0x09]`.
example :=
  unified_wide_scalar_field_decode_and_copy (0x1000 : Word) (0x2000 : Word) .x18
    (0x4000 : Word) 0
    [(0x89 : Byte), 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09] 0
    [(0x01 : Byte), 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09] []
    (List.replicate 9 (0 : Byte)) 0 0 0 0 0 0 0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro i hi
        have h10 : i < 10 := hi
        interval_cases i <;> decide)
    (by decide) (by decide) (by decide)
    (by intro i hi
        have h9 : i < 9 := by simpa using hi
        interval_cases i <;> decide)
    (by decide) (by decide)

end EvmAsm.Rv64.RLP
