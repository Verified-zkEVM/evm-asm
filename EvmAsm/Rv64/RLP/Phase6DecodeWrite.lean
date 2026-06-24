/-
  EvmAsm.Rv64.RLP.Phase6DecodeWrite

  EL.3 / Phase 6 — `decode ⨾ write_output`. Composes the end-to-end RLP-list schema decoder
  (`decode_encoded_short_list_schema_values`, which decodes the record into the output
  `bytesRegion` and recovers every field value via `schemaScalarValues`) with the `write_output`
  wrapper (`rlp_phase6_write_output_spec_within_exact`), so the decoded output region is committed
  to the host public-values stream.

  The decoder's `schemaINV` post exposes the scratch registers as `regOwn`, so the write wrapper
  is first lifted to a `regOwn` precondition (`rlp_phase6_write_output_spec_regOwn`) before the
  `cpsTripleWithin_seq`; the decoder-leftover state (input pointer/region, x0/x12/x14/x15) is
  framed through the write, and the ECALL instruction + initial public values are framed through
  the decode. The reshaping between the decoder post and the write pre is the standard
  `cpsTripleWithin_weaken … xperm_hyp` permutation (same idiom as `unified_scalar_field_decode_and_store`).
-/

import EvmAsm.Rv64.RLP.Phase6WriteOutput
import EvmAsm.Rv64.RLP.SchemaDecodeValues

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

-- ============================================================================
-- `regOwn`-precondition write wrapper: x10/x11/x5 abstracted so the wrapper is
-- callable directly on a decoder's `schemaINV` post (which releases them as `regOwn`).
-- ============================================================================

/-- The `write_output` wrapper with its three clobbered scratch registers (`x10`, `x11`, `x5`)
    owned abstractly (`regOwn`) in the precondition — the form a decoder's `schemaINV` post
    supplies. Derived from `rlp_phase6_write_output_spec_within_exact` by peeling each scratch
    register via `cpsTripleWithin_of_forall_regIs_to_regOwn`. -/
theorem rlp_phase6_write_output_spec_regOwn
    (rOut : Reg) (outBase : Word) (out old : List (BitVec 8)) (base : Word)
    (halign : outBase.toNat % 8 = 0) (hover : outBase.toNat + out.length < 2 ^ 64) :
    cpsTripleWithin 4 base (base + 16)
      (CodeReq.ofProg base (rlp_phase6_write_output_prog rOut (BitVec.ofNat 64 out.length)))
      ((rOut ↦ᵣ outBase) ** regOwn .x10 ** regOwn .x11 ** regOwn .x5 **
        (base + 12 ↦ᵢ .ECALL) ** bytesRegion outBase out ** publicValuesIs old)
      ((rOut ↦ᵣ outBase) ** (.x10 ↦ᵣ outBase) ** (.x11 ↦ᵣ (BitVec.ofNat 64 out.length)) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0x10)) ** (base + 12 ↦ᵢ .ECALL) **
        bytesRegion outBase out ** publicValuesIs (old ++ out)) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
      (P := (rOut ↦ᵣ outBase) ** regOwn .x10 ** regOwn .x11 **
        (base + 12 ↦ᵢ .ECALL) ** bytesRegion outBase out ** publicValuesIs old)
      (fun v5 => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x11)
      (P := (rOut ↦ᵣ outBase) ** regOwn .x10 ** (.x5 ↦ᵣ v5) **
        (base + 12 ↦ᵢ .ECALL) ** bytesRegion outBase out ** publicValuesIs old)
      (fun v11 => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x10)
      (P := (rOut ↦ᵣ outBase) ** (.x11 ↦ᵣ v11) ** (.x5 ↦ᵣ v5) **
        (base + 12 ↦ᵢ .ECALL) ** bytesRegion outBase out ** publicValuesIs old)
      (fun v10 => ?_))
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (rlp_phase6_write_output_spec_within_exact rOut outBase out old v10 v11 v5 base halign hover)

set_option maxRecDepth 8000 in
/-- **Decode a short-list RLP record, then commit it.** Runs the end-to-end schema decoder
    (`decode_encoded_short_list_schema_values`) — decoding the record into `bytesRegion outBase
    (schemaOut out specs)` and recovering every field value (`schemaScalarValues`) — then the
    `write_output` wrapper, appending the decoded output region to the host public-values stream
    (`publicValuesIs old → publicValuesIs (old ++ schemaOut out specs)`). The write code sits at
    `base_w := (base+148) + schemaSize specs` (the decoder's exit). -/
theorem rlp_phase6_decode_and_write
    (base regionBase outBase : Word) (rOut : Reg) (bs : List Byte) (O : Nat)
    (specs : List FieldSpec) (out old : List Byte) (outLen : Nat) (tail : List Byte)
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
    (hcode : base.toNat + (148 + schemaSize specs + 16) < 2 ^ 64) :
    cpsTripleWithin ((61 + schemaSteps specs) + 4) base
        (((base + 148) + BitVec.ofNat 64 (schemaSize specs)) + 16)
      ((((CodeReq.singleton base (.LBU .x5 .x13 0)).union
          (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
          (schemaCR (base + 148) rOut specs)).union
        (CodeReq.ofProg ((base + 148) + BitVec.ofNat 64 (schemaSize specs))
          (rlp_phase6_write_output_prog rOut (BitVec.ofNat 64 (schemaOut out specs).length))))
      (((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
        (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
        (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) **
       ((rOut ↦ᵣ outBase) ** bytesRegion outBase out) **
       ((((base + 148) + BitVec.ofNat 64 (schemaSize specs)) + 12 ↦ᵢ .ECALL) **
        publicValuesIs old))
      (((rOut ↦ᵣ outBase) ** (.x10 ↦ᵣ outBase) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 (schemaOut out specs).length)) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0x10)) **
        (((base + 148) + BitVec.ofNat 64 (schemaSize specs)) + 12 ↦ᵢ .ECALL) **
        bytesRegion outBase (schemaOut out specs) **
        publicValuesIs (old ++ schemaOut out specs)) **
       ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x12 **
        (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 ((O + 1) + schemaEnc specs))) **
        regOwn .x14 ** regOwn .x15 ** bytesRegion regionBase bs))
    ∧ schemaScalarValues bs (O + 1) specs := by
  -- The decoder.
  obtain ⟨t_dec, hvals⟩ := decode_encoded_short_list_schema_values base regionBase outBase rOut
    bs O specs out outLen tail v5Old v10 v11Old v12Old v14Old v15Old hsize hbs hcore halign hover
    hwin hdalign hlen hdov hdval (by omega)
  refine ⟨?_, hvals⟩
  -- Frame the ECALL instruction + the initial public values through the decode.
  have t_dec_f := cpsTripleWithin_frameR
    (((((base + 148) + BitVec.ofNat 64 (schemaSize specs)) + 12 ↦ᵢ .ECALL)) ** publicValuesIs old)
    (by exact pcFree_sepConj pcFree_instrAt pcFree_publicValuesIs) t_dec
  rw [schemaINV] at t_dec_f
  -- The decoded output region has length `outLen` (= out.length).
  have hsout : (schemaOut out specs).length = out.length := schemaOut_length out specs
  -- The write wrapper (regOwn scratch), framed with the decoder-leftover state it doesn't touch.
  have s_write0 := rlp_phase6_write_output_spec_regOwn rOut outBase (schemaOut out specs) old
    ((base + 148) + BitVec.ofNat 64 (schemaSize specs))
    hdalign (by rw [hsout, hlen]; exact hdov)
  -- Frame the decoder-leftover state (input region + scratch the write doesn't touch) onto the
  -- write wrapper.
  have s_write := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x12 **
      (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 ((O + 1) + schemaEnc specs))) **
      regOwn .x14 ** regOwn .x15 ** bytesRegion regionBase bs)
    (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regOwn
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regOwn
        (pcFree_sepConj pcFree_regOwn (bytesRegion_pcFree _ _))))))
    s_write0
  -- Disjointness: decoder CR (base .. base_w) ⊥ write CR (at base_w), by code ranges
  -- (`crDisjoint`/`seqFrame` time out on the opaque 36-instruction decoder `ofProg`).
  have hbw : ((base + 148) + BitVec.ofNat 64 (schemaSize specs)).toNat
      = base.toNat + 148 + schemaSize specs := by
    have : schemaSize specs < 2 ^ 64 := by omega
    bv_omega
  have hd : ((((CodeReq.singleton base (.LBU .x5 .x13 0)).union
        (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
        (schemaCR (base + 148) rOut specs))).Disjoint
      (CodeReq.ofProg ((base + 148) + BitVec.ofNat 64 (schemaSize specs))
        (rlp_phase6_write_output_prog rOut (BitVec.ofNat 64 (schemaOut out specs).length))) := by
    refine codeReq_disjoint_of_ranges _ _
      ((base + 148) + BitVec.ofNat 64 (schemaSize specs)).toNat ?_ ?_
    · intro a ha
      rw [hbw] at ha
      have h1 : CodeReq.singleton base (.LBU .x5 .x13 0) a = none :=
        CodeReq.singleton_miss (by bv_omega)
      have h2 : CodeReq.ofProg (base + 4) unified_decoder_prog a = none :=
        CodeReq.ofProg_none_range_len _ _ 36 a unified_decoder_prog_length
          (fun k hk => by bv_omega)
      have h3 : schemaCR (base + 148) rOut specs a = none :=
        schemaCR_none_above rOut specs (base + 148) a (by bv_omega) (by bv_omega)
      simp only [CodeReq.union, h1, h2, h3]
    · intro a ha
      rw [hbw] at ha
      exact CodeReq.ofProg_none_range_len _ _ 4 a rfl (fun k hk => by bv_omega)
  -- Provide `s_write` first so the middle assertion is pinned (concrete) before the reshape;
  -- the nested `refine` then resolves the target before the `xperm` goal is elaborated.
  refine cpsTripleWithin_seq hd ?_ s_write
  refine cpsTripleWithin_weaken ?_ ?_ t_dec_f
  · intro h hp; xperm_hyp hp
  · intro h hp; xperm_hyp hp

-- Concrete cross-check: decode the short RLP list `[0xc4, 0x2a, 0x82, 0x01, 0x02]`
-- (= `RLP.list [bytes [0x2a], bytes [0x01,0x02]]`) at region `0x2000` into a 24-byte output
-- struct at `0x3000` (via `x18`), then commit the struct to the public-values stream.
example :=
  rlp_phase6_decode_and_write (0x1000 : Word) (0x2000 : Word) (0x3000 : Word) .x18
    [(0xc4 : Byte), 0x2a, 0x82, 0x01, 0x02] 0
    [⟨true, [(0x2a : Byte)], 0, 0⟩, ⟨false, [(0x01 : Byte), (0x02 : Byte)], 8, 8⟩]
    (List.replicate 24 (0 : Byte)) [] 24 []
    0 0 0 0 0 0
    (by decide) (by decide)
    (by intro f hf; fin_cases hf <;> exact ⟨by decide, by decide, by decide⟩)
    (by decide) (by decide) (by decide) (by decide) (by simp) (by decide) (by decide) (by decide)

end EvmAsm.Rv64.RLP
