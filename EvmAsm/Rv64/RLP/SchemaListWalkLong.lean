/-
  EvmAsm.Rv64.RLP.SchemaListWalkLong

  EL.3 / Phase 5 — long-list specialization of `list_schema_walk`. Real STF structures
  (transactions, block headers) exceed 55 bytes, so they are encoded as LONG lists (RLP prefix
  `0xf8..0xff`): the prefix is followed by `lenOfLen` big-endian length bytes, then the payload.
  The payload therefore starts at `(O + 1) + lenOfLen`, and `regionLongWindow` requires those
  `lenOfLen` length bytes to be in-region — which follows from the global byte-access validity
  (`hwin`) plus a single "the length bytes fit in the buffer" bound. This discharges both, so a
  long-list schema decode needs only the prefix-class fact and that bound.
-/

import EvmAsm.Rv64.RLP.SchemaListWalk

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

set_option maxRecDepth 8000 in
/-- **Long-list schema decode.** As `list_schema_walk` but the list is known to be a long list
    (`classifyPrefix (bs[O]) = .longList`) whose `lenOfLen` length bytes fit in the buffer
    (`hlenbytes`); the payload offset `(O + 1) + lenOfLen` and the `regionLongWindow` are
    discharged automatically. -/
theorem long_list_schema_walk
    (base regionBase outBase : Word) (rOut : Reg) (bs : List Byte) (O : Nat) (hO : O < bs.length)
    (specs : List FieldSpec) (out : List Byte) (outLen : Nat)
    (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (hpfx : classifyPrefix (bs[O]'hO) = .longList)
    (hlenbytes : (O + 1) + rlpPrefixLongListLenOfLen (bs[O]'hO) ≤ bs.length)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hlen : out.length = outLen)
    (hdov : outBase.toNat + outLen < 2 ^ 64)
    (hdval : ∀ i, i < outLen → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hvalid : SchemaValid bs outLen ((O + 1) + rlpPrefixLongListLenOfLen (bs[O]'hO)) specs)
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
    ∧ schemaDecodes bs ((O + 1) + rlpPrefixLongListLenOfLen (bs[O]'hO)) specs :=
  list_schema_walk base regionBase outBase rOut bs O
    ((O + 1) + rlpPrefixLongListLenOfLen (bs[O]'hO)) hO specs out outLen
    v5Old v10 v11Old v12Old v14Old v15Old halign hover hwin
    (by simp only [regionLongWindow, hpfx]
        intro j hj
        exact ⟨by omega, hwin _ (by omega)⟩)
    (by simp only [itemPtrRegion, hpfx])
    hdalign hlen hdov hdval hvalid hcode

end EvmAsm.Rv64.RLP
