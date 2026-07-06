/-
  EvmAsm.Rv64.RLP.UnifiedBytesFieldRegOwn

  EL.3 / Phase 5 — `regOwn`-precondition variant of `unified_bytes_field_decode_and_copy`.
  The decode clobbers its scratch registers (`x5, x10, x11, x12`) and releases them as
  `regOwn` in its post; so to chain a byte-array field AFTER another field (which left
  those `regOwn`), the byte-array unit must accept `regOwn` scratch in its precondition.
  Peeling those four via `cpsTripleWithin_of_forall_regIs_to_regOwn` (à la the scalar
  `unified_scalar_field_decode_and_store_at_regOwn`) makes it chainable. `x14`/`x15` stay
  concrete (the prior field supplies them).
-/

import EvmAsm.Rv64.RLP.UnifiedBytesFieldDecode

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

set_option maxRecDepth 8000 in
/-- **`regOwn`-re-entry byte-array field decode-and-copy.** As
    `unified_bytes_field_decode_and_copy` but the four clobbered scratch registers
    (`x5, x10, x11, x12`) are owned abstractly (`regOwn`) in the precondition — callable
    after a prior field has run. -/
theorem unified_bytes_field_decode_and_copy_at_regOwn
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (data tail : List Byte) (outBytes : List Byte) (di0 : Nat)
    (v14Old v15Old : Word)
    (hlen1 : 1 ≤ data.length) (hlen55 : data.length ≤ 55)
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
      (((regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (regOwn .x11) **
        (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      (((regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes data)).length))) **
        (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + data.length))) ** (regOwn .x15) **
        (rOut ↦ᵣ outBase) ** bytesRegion regionBase bs **
        bytesRegion outBase (copyRangeGen outBytes data 0 di0 data.length)) **
       (regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 ** regOwn .x11))
    ∧ decode (bs.drop O) = some (.bytes data, tail) := by
  refine ⟨?_, ?_⟩
  · refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
        (P := (.x0 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs **
          ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes) **
          regOwn .x10 ** regOwn .x11 ** regOwn .x12)
        (fun v5 => ?_))
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x10)
        (P := (.x0 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs **
          ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes) **
          (.x5 ↦ᵣ v5) ** regOwn .x11 ** regOwn .x12)
        (fun v10 => ?_))
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x11)
        (P := (.x0 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs **
          ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes) **
          (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** regOwn .x12)
        (fun v11 => ?_))
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x12)
        (P := (.x0 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
          (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs **
          ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes) **
          (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11))
        (fun v12 => ?_))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (unified_bytes_field_decode_and_copy base regionBase rOut outBase fieldImm bs O data tail
        outBytes di0 v5 v10 v11 v12 v14Old v15Old hlen1 hlen55 hsize halign hdalign hover hwin
        hImm hdst hdov hdval hcode hdrop).1
  · exact (unified_bytes_field_decode_and_copy base regionBase rOut outBase fieldImm bs O data tail
      outBytes di0 0 0 0 0 v14Old v15Old hlen1 hlen55 hsize halign hdalign hover hwin
      hImm hdst hdov hdval hcode hdrop).2

end EvmAsm.Rv64.RLP
