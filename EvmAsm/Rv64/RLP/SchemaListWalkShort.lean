/-
  EvmAsm.Rv64.RLP.SchemaListWalkShort

  EL.3 / Phase 5 — short-list specialization of `list_schema_walk`. When the outer list is a
  SHORT list (RLP prefix `0xc0..0xf7`, payload ≤ 55 bytes), the payload starts at `O + 1` and
  the `regionLongWindow` precondition is vacuously `True` (only long forms carry length bytes).
  So a short-list schema decode needs neither the window nor the pointer-offset hypothesis — just
  the prefix-class fact `classifyPrefix (bs[O]) = .shortList`. This is the convenience entry point
  for short list-structured schemas.
-/

import EvmAsm.Rv64.RLP.SchemaListWalk

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

set_option maxRecDepth 8000 in
/-- **Short-list schema decode.** As `list_schema_walk` but the list is known to be a short list
    (`classifyPrefix (bs[O]) = .shortList`), so the payload offset (`O + 1`) and the trivial
    `regionLongWindow` are discharged automatically. -/
theorem short_list_schema_walk
    (base regionBase outBase : Word) (rOut : Reg) (bs : List Byte) (O : Nat) (hO : O < bs.length)
    (specs : List FieldSpec) (out : List Byte) (outLen : Nat)
    (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (hpfx : classifyPrefix (bs[O]'hO) = .shortList)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hlen : out.length = outLen)
    (hdov : outBase.toNat + outLen < 2 ^ 64)
    (hdval : ∀ i, i < outLen → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hvalid : SchemaValid bs outLen (O + 1) specs)
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
    ∧ schemaDecodes bs (O + 1) specs :=
  list_schema_walk base regionBase outBase rOut bs O (O + 1) hO specs out outLen
    v5Old v10 v11Old v12Old v14Old v15Old halign hover hwin
    (by simp only [regionLongWindow, hpfx])
    (by simp only [itemPtrRegion, hpfx])
    hdalign hlen hdov hdval hvalid hcode

end EvmAsm.Rv64.RLP
