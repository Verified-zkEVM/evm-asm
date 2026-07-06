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

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
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

end EvmAsm.Rv64.RLP
