/-
  EvmAsm.Rv64.RLP.Phase6Pipeline

  EL.3 / Phase 6 — the **complete top-level RLP pipeline**: `read_input ⨾ decode ⨾ write_output`.
  Composes the read⨾decode unit (`rlp_phase6_read_and_decode`) with the `write_output` wrapper
  (`rlp_phase6_write_output_spec_regOwn`): the host `read_input` syscall hands the RLP buffer to
  the schema decoder, which decodes the record into the output `bytesRegion`, and `write_output`
  commits that region to the host public-values stream.

  From the host-ABI input contract (`inputBufBaseIs buf_base`, `privateInputIs input`,
  `bytesRegion buf_base input` with `input = encode (.list (schemaItems specs)) ++ tail`), the whole
  program runs end to end in `(5 + (61 + schemaSteps specs)) + 4` steps, leaving
  `publicValues = old ++ schemaOut out specs` and recovering every field value
  (`schemaScalarValues`). This closes the RLP arc: RLP bytes in → decode → committed output, with a
  kernel-checkable round-trip proof against the pure RLP spec.
-/

import EvmAsm.Rv64.RLP.Phase6ReadDecode
import EvmAsm.Rv64.RLP.Phase6DecodeWrite

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

set_option maxRecDepth 8000 in
/-- **The full RLP pipeline: read ⨾ decode ⨾ write.** From the host-ABI input contract, run the
    `read_input` syscall + `LD` (input-pointer hand-off), the schema decoder, and the `write_output`
    syscall. The decoded output region is committed to the public-values stream
    (`publicValuesIs old → publicValuesIs (old ++ schemaOut out specs)`) and every field value is
    recovered (`schemaScalarValues`). The write code sits at `base_w := (base+20+148) + schemaSize`. -/
theorem rlp_phase6_read_decode_write
    (ptr_ptr_off size_ptr_off : BitVec 12) (rOut : Reg)
    (sp buf_base outBase old_ptr old_size v10 v11 v5 v13 v14 v15 : Word)
    (input : List (BitVec 8)) (out old : List Byte) (outLen : Nat) (tail : List Byte)
    (specs : List FieldSpec) (base : Word)
    (hvalid_a0 : isValidDwordAccess (sp + signExtend12 ptr_ptr_off) = true)
    (hvalid_a1 : isValidDwordAccess (sp + signExtend12 size_ptr_off) = true)
    (hsize : (schemaEncBytes specs).length ≤ 55)
    (hinput : input = encode (.list (schemaItems specs)) ++ tail)
    (hcore : ∀ f, f ∈ specs → fieldCoreValid outLen f)
    (halign : buf_base.toNat % 8 = 0)
    (hover : buf_base.toNat + input.length < 2 ^ 64)
    (hwin : ∀ i, i < input.length → isValidByteAccess (buf_base + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hlen : out.length = outLen)
    (hdov : outBase.toNat + outLen < 2 ^ 64)
    (hdval : ∀ i, i < outLen → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hcode : base.toNat + (20 + 148 + schemaSize specs + 16) < 2 ^ 64) :
    cpsTripleWithin ((5 + (61 + schemaSteps specs)) + 4) base
        (((base + 20 + 148) + BitVec.ofNat 64 (schemaSize specs)) + 16)
      ((((CodeReq.ofProg base (rlp_phase4_read_input_len_prog ptr_ptr_off size_ptr_off)).union
          (CodeReq.singleton (base + 16) (.LD .x13 .x12 ptr_ptr_off))).union
        (((CodeReq.singleton (base + 20) (.LBU .x5 .x13 0)).union
            (CodeReq.ofProg (base + 20 + 4) unified_decoder_prog)).union
          (schemaCR (base + 20 + 148) rOut specs))).union
        (CodeReq.ofProg ((base + 20 + 148) + BitVec.ofNat 64 (schemaSize specs))
          (rlp_phase6_write_output_prog rOut (BitVec.ofNat 64 (schemaOut out specs).length))))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x5 ↦ᵣ v5) ** (.x13 ↦ᵣ v13) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (rOut ↦ᵣ outBase) **
        (base + 12 ↦ᵢ .ECALL) **
        ((sp + signExtend12 ptr_ptr_off) ↦ₘ old_ptr) **
        ((sp + signExtend12 size_ptr_off) ↦ₘ old_size) **
        inputBufBaseIs buf_base ** privateInputIs input **
        bytesRegion buf_base input ** bytesRegion outBase out **
        ((((base + 20 + 148) + BitVec.ofNat 64 (schemaSize specs)) + 12 ↦ᵢ .ECALL) **
         publicValuesIs old))
      (((rOut ↦ᵣ outBase) ** (.x10 ↦ᵣ outBase) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 (schemaOut out specs).length)) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0x10)) **
        (((base + 20 + 148) + BitVec.ofNat 64 (schemaSize specs)) + 12 ↦ᵢ .ECALL) **
        bytesRegion outBase (schemaOut out specs) **
        publicValuesIs (old ++ schemaOut out specs)) **
       ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x12 **
        (.x13 ↦ᵣ (buf_base + BitVec.ofNat 64 ((0 + 1) + schemaEnc specs))) **
        regOwn .x14 ** regOwn .x15 ** bytesRegion buf_base input **
        (base + 12 ↦ᵢ .ECALL) **
        ((sp + signExtend12 ptr_ptr_off) ↦ₘ buf_base) **
        ((sp + signExtend12 size_ptr_off) ↦ₘ (BitVec.ofNat 64 input.length)) **
        inputBufBaseIs buf_base ** privateInputIs input))
    ∧ schemaScalarValues input (0 + 1) specs := by
  -- read ⨾ decode (steps 54–55).
  obtain ⟨t_rd, hvals⟩ := rlp_phase6_read_and_decode ptr_ptr_off size_ptr_off rOut sp buf_base
    outBase old_ptr old_size v10 v11 v5 v13 v14 v15 input out outLen tail specs base
    hvalid_a0 hvalid_a1 hsize hinput hcore halign hover hwin hdalign hlen hdov hdval (by omega)
  refine ⟨?_, hvals⟩
  -- Frame the write ECALL instruction + initial public values through read⨾decode.
  have t_rd_f := cpsTripleWithin_frameR
    (((((base + 20 + 148) + BitVec.ofNat 64 (schemaSize specs)) + 12 ↦ᵢ .ECALL)) **
      publicValuesIs old)
    (by exact pcFree_sepConj pcFree_instrAt pcFree_publicValuesIs) t_rd
  rw [schemaINV] at t_rd_f
  have hsout : (schemaOut out specs).length = out.length := schemaOut_length out specs
  -- The write wrapper (regOwn scratch), framed with all the read⨾decode-leftover state.
  have s_write0 := rlp_phase6_write_output_spec_regOwn rOut outBase (schemaOut out specs) old
    ((base + 20 + 148) + BitVec.ofNat 64 (schemaSize specs))
    hdalign (by rw [hsout, hlen]; exact hdov)
  have s_write := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x12 **
      (.x13 ↦ᵣ (buf_base + BitVec.ofNat 64 ((0 + 1) + schemaEnc specs))) **
      regOwn .x14 ** regOwn .x15 ** bytesRegion buf_base input **
      (base + 12 ↦ᵢ .ECALL) **
      ((sp + signExtend12 ptr_ptr_off) ↦ₘ buf_base) **
      ((sp + signExtend12 size_ptr_off) ↦ₘ (BitVec.ofNat 64 input.length)) **
      inputBufBaseIs buf_base ** privateInputIs input)
    (by
      repeat (first
        | apply pcFree_sepConj
        | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_instrAt
        | exact pcFree_memIs | exact pcFree_inputBufBaseIs | exact pcFree_privateInputIs
        | exact bytesRegion_pcFree _ _))
    s_write0
  -- Disjointness: read⨾decode CR (base .. base_w) ⊥ write CR (at base_w), by ranges.
  have hbw : ((base + 20 + 148) + BitVec.ofNat 64 (schemaSize specs)).toNat
      = base.toNat + 20 + 148 + schemaSize specs := by
    have : schemaSize specs < 2 ^ 64 := by omega
    bv_omega
  have hd : ((((CodeReq.ofProg base (rlp_phase4_read_input_len_prog ptr_ptr_off size_ptr_off)).union
        (CodeReq.singleton (base + 16) (.LD .x13 .x12 ptr_ptr_off))).union
        (((CodeReq.singleton (base + 20) (.LBU .x5 .x13 0)).union
            (CodeReq.ofProg (base + 20 + 4) unified_decoder_prog)).union
          (schemaCR (base + 20 + 148) rOut specs)))).Disjoint
      (CodeReq.ofProg ((base + 20 + 148) + BitVec.ofNat 64 (schemaSize specs))
        (rlp_phase6_write_output_prog rOut (BitVec.ofNat 64 (schemaOut out specs).length))) := by
    refine codeReq_disjoint_of_ranges _ _
      ((base + 20 + 148) + BitVec.ofNat 64 (schemaSize specs)).toNat ?_ ?_
    · intro a ha
      rw [hbw] at ha
      have hp1 : CodeReq.ofProg base (rlp_phase4_read_input_len_prog ptr_ptr_off size_ptr_off) a = none :=
        CodeReq.ofProg_none_range_len base _ 4 a
          (rlp_phase4_read_input_len_prog_length ptr_ptr_off size_ptr_off) (fun k hk => by bv_omega)
      have hp2 : CodeReq.singleton (base + 16) (.LD .x13 .x12 ptr_ptr_off) a = none :=
        CodeReq.singleton_miss (by bv_omega)
      have hq1 : CodeReq.singleton (base + 20) (.LBU .x5 .x13 0) a = none :=
        CodeReq.singleton_miss (by bv_omega)
      have hq2 : CodeReq.ofProg (base + 20 + 4) unified_decoder_prog a = none :=
        CodeReq.ofProg_none_range_len (base + 20 + 4) unified_decoder_prog 36 a
          unified_decoder_prog_length (fun k hk => by bv_omega)
      have hq3 : schemaCR (base + 20 + 148) rOut specs a = none :=
        schemaCR_none_above rOut specs (base + 20 + 148) a (by bv_omega) (by bv_omega)
      simp only [CodeReq.union, hp1, hp2, hq1, hq2, hq3]
    · intro a ha
      rw [hbw] at ha
      exact CodeReq.ofProg_none_range_len _ _ 4 a rfl (fun k hk => by bv_omega)
  -- Provide `s_write` first so the middle assertion is concrete before the reshape.
  refine cpsTripleWithin_seq hd ?_ s_write
  refine cpsTripleWithin_weaken ?_ ?_ t_rd_f
  · intro h hp; xperm_hyp hp
  · intro h hp; xperm_hyp hp

-- Concrete end-to-end cross-check of the WHOLE pipeline: the host supplies the short RLP list
-- `[0xc4, 0x2a, 0x82, 0x01, 0x02]` (= `RLP.list [bytes [0x2a], bytes [0x01,0x02]]`) at the input
-- buffer `0x2000` (via the `read_input` syscall through SP-relative cells at `0x5000`/`0x5008`);
-- the program decodes it into the 24-byte output struct at `0x3000` (via `x18`) and commits that
-- struct to the public-values stream. Program base `0x1000`.
example :=
  rlp_phase6_read_decode_write (0 : BitVec 12) (8 : BitVec 12) .x18
    (0x5000 : Word) (0x2000 : Word) (0x3000 : Word) 0 0 0 0 0 0 0 0
    [(0xc4 : Byte), 0x2a, 0x82, 0x01, 0x02]
    (List.replicate 24 (0 : Byte)) [] 24 []
    [⟨true, [(0x2a : Byte)], 0, 0⟩, ⟨false, [(0x01 : Byte), (0x02 : Byte)], 8, 8⟩]
    (0x1000 : Word)
    (by decide) (by decide) (by decide) (by decide)
    (by intro f hf; fin_cases hf <;> exact ⟨by decide, by decide, by decide⟩)
    (by decide) (by decide) (by decide) (by decide) (by simp) (by decide) (by decide) (by decide)

end EvmAsm.Rv64.RLP
