/-
  Per-iteration straight-line building blocks for
  `chain_validate_increasing_timestamps`.

  Builds on `ChainValidateIncreasingTimestampsSpec` (model, prologue, epilogue,
  exit blocks).  The distinguishing feature of this CROSS-HEADER accessor is the
  spill/reload of the iterator state — `{base_i, i, prev = ts[i-1]}` — through
  the scratch cells `cvit_iter_child` / `cvit_iter_i` / `cvit_iter_prev` around
  each `rlp_field_to_u64` (field 11) call, and the `BGEU x29 x28` comparison of
  the reloaded `prev` (`cvit_iter_prev`) against the freshly-decoded `cur`
  (`cvit_ts`).  The `prev` cell genuinely holds the ACTUAL decoded timestamp of
  header `i-1` (tied to K34's `Result`), so the invariant threads the real value.
-/

import EvmAsm.Codegen.Programs.ChainValidateIncreasingTimestampsSpec
import EvmAsm.Evm64.StateAssertions

namespace EvmAsm.Codegen.ChainValidateIncreasingTimestampsSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm
  (Saved savedFrame savedVals listNthFrame regsAt_listNthFrame
   frameSlotsSaved_listNthFrame)
open EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
  (wordArray wordArrayFrom wordArray_split pcFree_wordArray pcFree_wordArrayFrom
   wordArrayFrom_append shiftLeft3_ofNat hdrOff hdrBaseAt hdrOff_succ hdrBaseAt_succ
   ofNat_ne_of_lt ofNat_succ_tie)

/-! ## Spill block (instructions 32--40): spill `{child, i, prev}` to scratch

    From the loop-guard fall-through (`D+128`) to just before the argument setup
    (`D+164`).  Materializes `*cvit_iter_child := base_i`, `*cvit_iter_i := i`,
    and — crucially — `*cvit_iter_prev := prev` where `prev` is `x21`, the
    timestamp decoded from header `i-1`. -/

set_option maxRecDepth 8000 in
theorem cvitSpill (hbi iW prevVal old5 : Word) :
    cpsTripleWithin 9 (D + 128) (D + 164) cvitCode
      ((.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ hbi) ** (.x7 ↦ᵣ iW) ** (.x21 ↦ᵣ prevVal) **
        memOwn IterChild ** memOwn IterI ** memOwn IterPrev)
      ((.x5 ↦ᵣ IterPrev) ** (.x6 ↦ᵣ hbi) ** (.x7 ↦ᵣ iW) ** (.x21 ↦ᵣ prevVal) **
        (IterChild ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (IterPrev ↦ₘ prevVal)) := by
  have hla32 := la_materialize_within .x5 old5 (D + 128) IterChild (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 128) cvitProg 32 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 128) IterChild)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 132) cvitProg 33 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 128) IterChild)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
  have s34 := sd_spec_gen_own_within .x5 .x6 IterChild hbi (0 : BitVec 12) (D + 136)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterChild + (0 : Word) = IterChild from by bv_omega] at s34
  have s34' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 136) cvitProg 34 (.SD .x5 .x6 (0 : BitVec 12))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s34
  have hla35 := la_materialize_within .x5 IterChild (D + 140) IterI (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 140) cvitProg 35 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 140) IterI)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 144) cvitProg 36 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 140) IterI)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
  have s37 := sd_spec_gen_own_within .x5 .x7 IterI iW (0 : BitVec 12) (D + 148)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterI + (0 : Word) = IterI from by bv_omega] at s37
  have s37' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 148) cvitProg 37 (.SD .x5 .x7 (0 : BitVec 12))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s37
  have hla38 := la_materialize_within .x5 IterI (D + 152) IterPrev (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 152) cvitProg 38 (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 152) IterPrev)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 156) cvitProg 39 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 152) IterPrev)) (by bv_omega) (by rw [cvit_length]; decide) (by decide) (by rw [cvit_length]; decide))
  have s40 := sd_spec_gen_own_within .x5 .x21 IterPrev prevVal (0 : BitVec 12) (D + 160)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterPrev + (0 : Word) = IterPrev from by bv_omega] at s40
  have s40' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 160) cvitProg 40 (.SD .x5 .x21 (0 : BitVec 12))
      (by bv_omega) (by rw [cvit_length]; decide) rfl (by rw [cvit_length]; decide)) s40
  runBlock hla32 s34' hla35 s37' hla38 s40'

#print axioms cvitSpill

end EvmAsm.Codegen.ChainValidateIncreasingTimestampsSpec
