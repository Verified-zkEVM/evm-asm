/-
  EvmAsm.Rv64.RLP.UnifiedLongBytesFieldCanonical

  EL.3 / Phase 5 — the canonical re-entry chain for the LONG byte-array field unit
  (`UnifiedLongBytesField`, `data.length > 55`), exactly paralleling the short byte-array
  chain (`_at_regOwn` → `_canonical` → `_fully_canonical`). Because the long unit has the
  identical scratch pre/post/CR/step shape as the short unit (only the payload-window proof
  differs), each peeling layer is the same as its short counterpart with the underlying unit
  swapped. The endpoint, `unified_long_bytes_field_decode_and_copy_fully_canonical`, has the
  uniform all-`regOwn` scratch interface the N-field fold (`schema_walk`) consumes — the
  prerequisite for integrating `> 55`-byte fields (calldata, the 256-byte `logsBloom`) into
  the schema engine.
-/

import EvmAsm.Rv64.RLP.UnifiedLongBytesField
import EvmAsm.Rv64.RLP.FieldUnitDisjoint

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

set_option maxRecDepth 8000 in
/-- **`regOwn`-re-entry long byte-array field decode-and-copy.** As
    `unified_long_bytes_field_decode_and_copy` but the four clobbered scratch registers
    (`x5, x10, x11, x12`) are `regOwn` in the precondition — callable after a prior field. -/
theorem unified_long_bytes_field_decode_and_copy_at_regOwn
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (data tail : List Byte) (outBytes : List Byte) (di0 : Nat)
    (v14Old v15Old : Word)
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
      (unified_long_bytes_field_decode_and_copy base regionBase rOut outBase fieldImm bs O data tail
        outBytes di0 v5 v10 v11 v12 v14Old v15Old hlong hsize halign hdalign hover hwin
        hImm hdst hdov hdval hcode hdrop).1
  · exact (unified_long_bytes_field_decode_and_copy base regionBase rOut outBase fieldImm bs O data tail
      outBytes di0 0 0 0 0 v14Old v15Old hlong hsize halign hdalign hover hwin
      hImm hdst hdov hdval hcode hdrop).2

set_option maxRecDepth 8000 in
/-- **Canonical long byte-array field decode-and-copy.** As `…_at_regOwn` but `x15` is also
    `regOwn` in the precondition — the uniform `x5, x10, x11, x12, x15` interface. -/
theorem unified_long_bytes_field_decode_and_copy_canonical
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (data tail : List Byte) (outBytes : List Byte) (di0 : Nat)
    (v14Old : Word)
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
    cpsTripleWithin (61 + (1 + 5 * data.length)) base
        (base + 148 + 4 + BitVec.ofNat 64 (20 * data.length))
      (bytesUnitCR base rOut fieldImm data.length)
      (((regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (regOwn .x11) **
        (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
        (regOwn .x15) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      (((regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes data)).length))) **
        (.x14 ↦ᵣ (outBase + BitVec.ofNat 64 (di0 + data.length))) ** (regOwn .x15) **
        (rOut ↦ᵣ outBase) ** bytesRegion regionBase bs **
        bytesRegion outBase (copyRangeGen outBytes data 0 di0 data.length)) **
       (regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 ** regOwn .x11))
    ∧ decode (bs.drop O) = some (.bytes data, tail) := by
  refine ⟨?_, ?_⟩
  · refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x15)
        (P := (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (regOwn .x11) **
          (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
          bytesRegion regionBase bs ** ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
        (fun v15 => ?_))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (unified_long_bytes_field_decode_and_copy_at_regOwn base regionBase rOut outBase fieldImm bs O data
        tail outBytes di0 v14Old v15 hlong hsize halign hdalign hover hwin hImm hdst hdov
        hdval hcode hdrop).1
  · exact (unified_long_bytes_field_decode_and_copy_at_regOwn base regionBase rOut outBase fieldImm bs O
      data tail outBytes di0 v14Old 0 hlong hsize halign hdalign hover hwin hImm hdst hdov
      hdval hcode hdrop).2

set_option maxRecDepth 8000 in
/-- **Fully-canonical long byte-array field unit.** As `…_canonical` but `x14` is also `regOwn`
    in both pre and post — the fully uniform scratch interface (`x5, x10, x11, x12, x14, x15`)
    the N-field fold consumes. -/
theorem unified_long_bytes_field_decode_and_copy_fully_canonical
    (base regionBase : Word) (rOut : Reg) (outBase : Word) (fieldImm : BitVec 12)
    (bs : List Byte) (O : Nat) (data tail : List Byte) (outBytes : List Byte) (di0 : Nat)
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
    cpsTripleWithin (61 + (1 + 5 * data.length)) base
        (base + 148 + 4 + BitVec.ofNat 64 (20 * data.length))
      (bytesUnitCR base rOut fieldImm data.length)
      (((regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (regOwn .x11) **
        (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (regOwn .x14) **
        (regOwn .x15) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
      (((regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes data)).length))) **
        (regOwn .x14) ** (regOwn .x15) **
        (rOut ↦ᵣ outBase) ** bytesRegion regionBase bs **
        bytesRegion outBase (copyRangeGen outBytes data 0 di0 data.length)) **
       (regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 ** regOwn .x11))
    ∧ decode (bs.drop O) = some (.bytes data, tail) := by
  refine ⟨?_, ?_⟩
  · refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
      (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x14)
        (P := (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) ** (regOwn .x11) **
          (regOwn .x12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
          (regOwn .x15) ** bytesRegion regionBase bs ** ((rOut ↦ᵣ outBase) ** bytesRegion outBase outBytes))
        (fun v14 => ?_))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (regIs_implies_regOwn .x14)))))
      (unified_long_bytes_field_decode_and_copy_canonical base regionBase rOut outBase fieldImm bs O data
        tail outBytes di0 v14 hlong hsize halign hdalign hover hwin hImm hdst hdov hdval
        hcode hdrop).1
  · exact (unified_long_bytes_field_decode_and_copy_canonical base regionBase rOut outBase fieldImm bs O
      data tail outBytes di0 0 hlong hsize halign hdalign hover hwin hImm hdst hdov hdval
      hcode hdrop).2

end EvmAsm.Rv64.RLP
