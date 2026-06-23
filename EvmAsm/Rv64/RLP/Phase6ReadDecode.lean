/-
  EvmAsm.Rv64.RLP.Phase6ReadDecode

  EL.3 / Phase 6 — the top-level pipeline's input hand-off: `read_input ⨾ LD`. The
  `read_input` Phase-4 wrapper (`rlp_phase4_read_input_len_spec_within_exact`) calls the
  zkvm-standards `read_input` syscall, writing `inputBufBase` and `privateInput.length` to two
  SP-relative cells. The schema decoder, however, wants the input buffer base in `x13` (its
  input pointer). This file bridges them: after the wrapper, one `LD x13, x12, ptr_ptr_off`
  loads `buf_base` from its cell into `x13`, leaving the machine ready for the decoder to run on
  `bytesRegion inputBufBase privateInput` (the host-ABI input contract, supplied by the caller).
-/

import EvmAsm.Rv64.RLP.Phase4HintLen
import EvmAsm.Rv64.RLP.SchemaDecodeValues
import EvmAsm.Rv64.InstructionSpecs

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

set_option maxRecDepth 8000 in
/-- **Phase 6 input-pointer hand-off.** Run the `read_input` wrapper (4 instrs) then
    `LD x13, x12, ptr_ptr_off` (1 instr) to load the returned `inputBufBase` into `x13` — the
    schema decoder's input pointer. The two out-cells end holding `(buf_base, input.length)` and
    `x13 = buf_base`; `inputBufBaseIs`/`privateInputIs` are preserved. -/
theorem rlp_phase6_read_input_ptr
    (ptr_ptr_off size_ptr_off : BitVec 12)
    (sp buf_base old_ptr old_size v10 v11 v5 v13 : Word)
    (input : List (BitVec 8)) (base : Word)
    (hvalid_a0 : isValidDwordAccess (sp + signExtend12 ptr_ptr_off) = true)
    (hvalid_a1 : isValidDwordAccess (sp + signExtend12 size_ptr_off) = true) :
    cpsTripleWithin 5 base (base + 20)
      ((CodeReq.ofProg base (rlp_phase4_read_input_len_prog ptr_ptr_off size_ptr_off)).union
        (CodeReq.singleton (base + 16) (.LD .x13 .x12 ptr_ptr_off)))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x5 ↦ᵣ v5) ** (.x13 ↦ᵣ v13) **
        (base + 12 ↦ᵢ .ECALL) **
        ((sp + signExtend12 ptr_ptr_off) ↦ₘ old_ptr) **
        ((sp + signExtend12 size_ptr_off) ↦ₘ old_size) **
        inputBufBaseIs buf_base ** privateInputIs input)
      ((.x12 ↦ᵣ sp) **
        (.x10 ↦ᵣ sp + signExtend12 ptr_ptr_off) **
        (.x11 ↦ᵣ sp + signExtend12 size_ptr_off) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0xF2)) **
        (.x13 ↦ᵣ buf_base) **
        (base + 12 ↦ᵢ .ECALL) **
        ((sp + signExtend12 ptr_ptr_off) ↦ₘ buf_base) **
        ((sp + signExtend12 size_ptr_off) ↦ₘ (BitVec.ofNat 64 input.length)) **
        inputBufBaseIs buf_base ** privateInputIs input) := by
  -- The read_input wrapper, framing x13 through it.
  have h_read := rlp_phase4_read_input_len_spec_within_exact ptr_ptr_off size_ptr_off
    sp buf_base old_ptr old_size v10 v11 v5 input base hvalid_a0 hvalid_a1
  have h_read' := cpsTripleWithin_frameR (.x13 ↦ᵣ v13) (by pcFree) h_read
  -- The load: LD x13, x12, ptr_ptr_off reads buf_base from its cell into x13.
  have h_ld := ld_spec_within .x13 .x12 sp v13 buf_base ptr_ptr_off (base + 16) (by decide)
  have h_ld' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ sp + signExtend12 ptr_ptr_off) ** (.x11 ↦ᵣ sp + signExtend12 size_ptr_off) **
      (.x5 ↦ᵣ (BitVec.ofNat 64 0xF2)) ** (base + 12 ↦ᵢ .ECALL) **
      ((sp + signExtend12 size_ptr_off) ↦ₘ (BitVec.ofNat 64 input.length)) **
      inputBufBaseIs buf_base ** privateInputIs input)
    (by pcFree) h_ld
  -- Disjointness: the wrapper code (base .. base+12) ⊥ the LD at base+16.
  have hd : (CodeReq.ofProg base (rlp_phase4_read_input_len_prog ptr_ptr_off size_ptr_off)).Disjoint
      (CodeReq.singleton (base + 16) (.LD .x13 .x12 ptr_ptr_off)) :=
    CodeReq.Disjoint.ofProg_singleton
      (CodeReq.ofProg_none_range_len base (rlp_phase4_read_input_len_prog ptr_ptr_off size_ptr_off) 4
        (base + 16) (rlp_phase4_read_input_len_prog_length ptr_ptr_off size_ptr_off)
        (by intro k hk; bv_omega))
  have composed := cpsTripleWithin_seq hd
    (cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp) h_read')
    h_ld'
  rw [show base + 16 + 4 = base + 20 from by bv_omega,
      show (4 : Nat) + 1 = 5 from rfl] at composed
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) composed

set_option maxRecDepth 8000 in
/-- **Phase 6 read ⨾ decode.** The input-pointer hand-off (`rlp_phase6_read_input_ptr`) composed
    with the short-list schema decoder. From the host-ABI input contract — `inputBufBaseIs buf_base`,
    `privateInputIs input`, and `bytesRegion buf_base input` (the host placed the RLP input at the
    aligned, readable input buffer) — with `input = encode (.list (schemaItems specs)) ++ tail`, the
    `read_input` syscall + `LD` + decoder run end to end: the field record is decoded into the output
    region (`bytesRegion outBase (schemaOut out specs)`), with each field's value recovered
    (`schemaScalarValues`). -/
theorem rlp_phase6_read_and_decode
    (ptr_ptr_off size_ptr_off : BitVec 12) (rOut : Reg)
    (sp buf_base outBase old_ptr old_size v10 v11 v5 v13 v14 v15 : Word)
    (input : List (BitVec 8)) (out : List Byte) (outLen : Nat) (tail : List Byte)
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
    (hcode : base.toNat + (20 + 148 + schemaSize specs) < 2 ^ 64) :
    cpsTripleWithin (5 + (61 + schemaSteps specs)) base
        ((base + 20 + 148) + BitVec.ofNat 64 (schemaSize specs))
      (((CodeReq.ofProg base (rlp_phase4_read_input_len_prog ptr_ptr_off size_ptr_off)).union
          (CodeReq.singleton (base + 16) (.LD .x13 .x12 ptr_ptr_off))).union
        (((CodeReq.singleton (base + 20) (.LBU .x5 .x13 0)).union
            (CodeReq.ofProg (base + 20 + 4) unified_decoder_prog)).union
          (schemaCR (base + 20 + 148) rOut specs)))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x5 ↦ᵣ v5) ** (.x13 ↦ᵣ v13) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (rOut ↦ᵣ outBase) **
        (base + 12 ↦ᵢ .ECALL) **
        ((sp + signExtend12 ptr_ptr_off) ↦ₘ old_ptr) **
        ((sp + signExtend12 size_ptr_off) ↦ₘ old_size) **
        inputBufBaseIs buf_base ** privateInputIs input **
        bytesRegion buf_base input ** bytesRegion outBase out)
      ((schemaINV buf_base outBase rOut input ((0 + 1) + schemaEnc specs) (schemaOut out specs)) **
        ((base + 12 ↦ᵢ .ECALL) **
         ((sp + signExtend12 ptr_ptr_off) ↦ₘ buf_base) **
         ((sp + signExtend12 size_ptr_off) ↦ₘ (BitVec.ofNat 64 input.length)) **
         inputBufBaseIs buf_base ** privateInputIs input))
    ∧ schemaScalarValues input (0 + 1) specs := by
  -- PR1: read_input ⨾ LD, leaving x13 = buf_base. Frame the decoder-extras through it.
  have h1 := rlp_phase6_read_input_ptr ptr_ptr_off size_ptr_off sp buf_base old_ptr old_size
    v10 v11 v5 v13 input base hvalid_a0 hvalid_a1
  have h1' := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (rOut ↦ᵣ outBase) **
      bytesRegion buf_base input ** bytesRegion outBase out)
    (by pcFree) h1
  -- The decoder at base+20, on bytesRegion buf_base input (O = 0).
  obtain ⟨t_dec, hvals⟩ := decode_encoded_short_list_schema_values (base + 20) buf_base outBase rOut
    input 0 specs out outLen tail (BitVec.ofNat 64 0xF2)
    (sp + signExtend12 ptr_ptr_off) (sp + signExtend12 size_ptr_off) sp v14 v15
    hsize (by rw [List.drop_zero]; exact hinput) hcore halign hover hwin hdalign hlen hdov hdval
    (by bv_omega)
  -- x13 in the decoder pre is `buf_base + ofNat 0`; normalise to `buf_base`.
  rw [show buf_base + BitVec.ofNat 64 0 = buf_base from by bv_omega] at t_dec
  -- Frame the read-leftovers (cells, ECALL, input assertions) through the decoder.
  have t_dec' := cpsTripleWithin_frameR
    ((base + 12 ↦ᵢ .ECALL) **
      ((sp + signExtend12 ptr_ptr_off) ↦ₘ buf_base) **
      ((sp + signExtend12 size_ptr_off) ↦ₘ (BitVec.ofNat 64 input.length)) **
      inputBufBaseIs buf_base ** privateInputIs input)
    (by pcFree) t_dec
  -- Disjointness: read+LD code (base .. base+20) ⊥ decoder code (≥ base+20).
  have hd : (((CodeReq.ofProg base (rlp_phase4_read_input_len_prog ptr_ptr_off size_ptr_off)).union
        (CodeReq.singleton (base + 16) (.LD .x13 .x12 ptr_ptr_off)))).Disjoint
      (((CodeReq.singleton (base + 20) (.LBU .x5 .x13 0)).union
          (CodeReq.ofProg (base + 20 + 4) unified_decoder_prog)).union
        (schemaCR (base + 20 + 148) rOut specs)) := by
    refine codeReq_disjoint_of_ranges _ _ (base.toNat + 20) ?_ ?_
    · intro a ha
      have hp1 : CodeReq.ofProg base (rlp_phase4_read_input_len_prog ptr_ptr_off size_ptr_off) a = none :=
        CodeReq.ofProg_none_range_len base _ 4 a
          (rlp_phase4_read_input_len_prog_length ptr_ptr_off size_ptr_off) (by intro k hk; bv_omega)
      have hp2 : CodeReq.singleton (base + 16) (.LD .x13 .x12 ptr_ptr_off) a = none :=
        CodeReq.singleton_miss (by bv_omega)
      simp only [CodeReq.union, hp1, hp2]
    · intro a ha
      have hq1 : CodeReq.singleton (base + 20) (.LBU .x5 .x13 0) a = none :=
        CodeReq.singleton_miss (by bv_omega)
      have hq2 : CodeReq.ofProg (base + 20 + 4) unified_decoder_prog a = none :=
        CodeReq.ofProg_none_range_len (base + 20 + 4) unified_decoder_prog 36 a
          unified_decoder_prog_length (by intro k hk; bv_omega)
      have hq3 : schemaCR (base + 20 + 148) rOut specs a = none :=
        schemaCR_none_below rOut specs (base + 20 + 148) a (by bv_omega) (by bv_omega)
      simp only [CodeReq.union, hq1, hq2, hq3]
  refine ⟨?_, hvals⟩
  have composed := cpsTripleWithin_seq hd
    (cpsTripleWithin_weaken (fun _ h => h) (fun _ hp => by xperm_hyp hp) h1') t_dec'
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h) composed

end EvmAsm.Rv64.RLP
