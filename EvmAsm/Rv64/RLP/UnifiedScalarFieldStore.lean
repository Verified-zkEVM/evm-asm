/-
  EvmAsm.Rv64.RLP.UnifiedScalarFieldStore

  EL.3 / Phase 5 — decode a scalar field AND STORE its value. Composes the
  end-to-end scalar field decode (`unified_scalar_field_decode`, which leaves the
  field value in `x11` and advances `x13` to the next field) with a single `SD`
  that writes that value to a fixed slot of an output struct (`outBase + offset`).

  This is the missing PERSISTENCE step: a multi-field schema walk decodes each
  field into `x11`, but the next field's decode clobbers `x11`, so every value
  must be written out before moving on. The output slots for scalar fields are
  u64 little-endian (nonce, gas_limit, to_present, v, …; see
  `EvmAsm/Stateless/Transaction/Decode.lean`), which is exactly what a single `SD`
  of the 64-bit value register produces. The result is the atomic, reusable unit
  the fixed-schema STF header/tx decoders repeat: decode one scalar field, store
  it, advance to the next.

  Layout (program base `base`; aligned `regionBase`, buffer `bs`, field offset `O`;
  output pointer register `rOut`, output base `outBase`, struct slot `offset`):
      base       < unified_scalar_field_decode : LBU + decoder + BE read >
                 (base .. base+180)                  ; x11 = value, x13 → next field
      base+180   SD rOut, x11, offset                ; [outBase + offset] := value
      base+184   (exit)
-/

import EvmAsm.Rv64.RLP.UnifiedScalarFieldDecode
import EvmAsm.Rv64.InstructionSpecs

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

set_option maxRecDepth 8000 in
/-- **Decode-and-store a scalar field.** From `x13 = regionBase + ofNat O` (a
    `.bytes data` scalar field, `1 ≤ data.length ≤ 8`), decode the field and write
    its value `Nat.fromBytesBE data` to the output cell `outBase + offset` via `SD`,
    advancing `x13` to the next field. The output pointer register `rOut` and the
    output cell are framed alongside the decode; `rOut` is intended to be a
    callee-saved register the decoder never touches (a clashing choice merely makes
    the precondition unsatisfiable). Coincides with the pure
    `decodeScalar (bs.drop O) = some (Nat.fromBytesBE data, tail)`. -/
theorem unified_scalar_field_decode_and_store
    (base regionBase : Word) (rOut : Reg) (outBase memOld : Word) (offset : BitVec 12)
    (bs : List Byte) (O : Nat) (data : List Byte) (tail : List Byte)
    (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (hlen1 : 1 ≤ data.length) (hlen8 : data.length ≤ 8)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdrop : bs.drop O = encode (.bytes data) ++ tail) :
    cpsTripleWithin (64 + 6 * data.length) base (base + 184)
      ((((CodeReq.singleton base (.LBU .x5 .x13 0)).union
          (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
          (((CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0)).union
              (CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0))).union
              (CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20))))).union
          (CodeReq.singleton (base + 180) (.SD rOut .x11 offset)))
      (((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
        (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** ((outBase + signExtend12 offset) ↦ₘ memOld)))
      (((rOut ↦ᵣ outBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE data)) **
        ((outBase + signExtend12 offset) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE data))) **
       ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes data)).length))) **
        regOwn .x14 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
        regOwn .x5 ** regOwn .x10 ** (.x15 ↦ᵣ v15Old)))
    ∧ decodeScalar (bs.drop O) = some (Nat.fromBytesBE data, tail) := by
  obtain ⟨t_dec, hpure⟩ := unified_scalar_field_decode base regionBase bs O data tail
    v5Old v10 v11Old v12Old v14Old v15Old hlen1 hlen8 halign hover hwin hdrop
  -- Frame the output pointer and cell alongside the decode.
  have t_dec_f := cpsTripleWithin_frameR
    ((rOut ↦ᵣ outBase) ** ((outBase + signExtend12 offset) ↦ₘ memOld)) (by pcFree) t_dec
  -- The store: SD rOut, x11, offset.
  have s_sd := sd_spec_within rOut .x11 outBase (BitVec.ofNat 64 (Nat.fromBytesBE data))
    memOld offset (base + 180)
  -- Frame the rest of the state (everything except rOut/x11/cell) around the store.
  have s_store := cpsTripleWithin_frameR
    ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode (.bytes data)).length))) **
     regOwn .x14 ** regOwn .x12 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
     regOwn .x5 ** regOwn .x10 ** (.x15 ↦ᵣ v15Old))
    (by pcFree) s_sd
  rw [show base + 180 + 4 = base + 184 from by bv_omega] at s_store
  -- Disjointness: the decoder/read CR (base .. base+176) ⊥ the store at base+180.
  have hd : ((((CodeReq.singleton base (.LBU .x5 .x13 0)).union
        (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
        (((CodeReq.singleton (base + 148) (.ADDI .x14 .x11 0)).union
            (CodeReq.singleton (base + 152) (.ADDI .x11 .x0 0))).union
            (CodeReq.ofProg (base + 156) (rlp_phase2_long_loop_body_prog (-20)))))).Disjoint
      (CodeReq.singleton (base + 180) (.SD rOut .x11 offset)) :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.singleton (by bv_omega))
        (CodeReq.Disjoint.ofProg_singleton
          (CodeReq.ofProg_none_range_len (base + 4) unified_decoder_prog 36 (base + 180)
            unified_decoder_prog_length (by intro k hk; bv_omega))))
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.union_left
          (CodeReq.Disjoint.singleton (by bv_omega))
          (CodeReq.Disjoint.singleton (by bv_omega)))
        (CodeReq.Disjoint.ofProg_singleton
          (CodeReq.ofProg_none_range_len (base + 156) (rlp_phase2_long_loop_body_prog (-20)) 6
            (base + 180) (by rfl) (by intro k hk; bv_omega))))
  refine ⟨?_, hpure⟩
  have composed := cpsTripleWithin_seq hd
    (cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp) t_dec_f)
    s_store
  rw [show (61 + (2 + 6 * data.length)) + 1 = 64 + 6 * data.length from by ring] at composed
  exact composed

-- Concrete cross-check: decode the single-byte scalar `0x2a` (= 42) at offset 0 of
-- the buffer `[0x2a]` from `0x2000`, storing the value to `0x3000` via `x18` ⇒ the
-- output cell `0x3000 ↦ₘ 0x2a` and `decodeScalar [0x2a] = some (42, [])`.
example :=
  unified_scalar_field_decode_and_store (0x1000 : Word) (0x2000 : Word) .x18
    (0x3000 : Word) 0 0 [(0x2a : Byte)] 0 [(0x2a : Byte)] [] 0 0 0 0 0 0
    (by decide) (by decide) (by decide) (by decide)
    (by intro i hi
        have hlen : ([(0x2a : Byte)]).length = 1 := by decide
        rw [hlen] at hi
        interval_cases i
        decide)
    (by decide)

end EvmAsm.Rv64.RLP
