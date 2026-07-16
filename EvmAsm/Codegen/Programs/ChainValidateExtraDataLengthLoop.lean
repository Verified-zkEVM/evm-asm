/-
  Per-iteration body + loop induction for `chain_validate_extra_data_length`.

  Builds on `ChainValidateExtraDataLengthSpec` (model, prologue, epilogue, exit
  blocks, `wordArray_split`) to prove the loop body `[C+72 … C+204]`, the loop
  induction `cvedlLoop` (on `N − i`), and the whole-program caller contract
  `chain_validate_extra_data_length_spec_within`.
-/

import EvmAsm.Codegen.Programs.ChainValidateExtraDataLengthSpec

namespace EvmAsm.Codegen.ChainValidateExtraDataLengthSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm


/-! ## Setup block (instructions 18--32): spill + array load + call-arg setup

    From the loop guard fall-through (`C+72`) to just before the `jal` (`C+132`).
    Fully generic in the current header base `hbi`, the counter word `iW`, and
    the field-length value `Li`; the loop supplies `hbi = hdrBaseAt …`,
    `iW = ofNat i`, `Li = lengths[i]`. -/

set_option maxRecDepth 8000 in
theorem cvedlSetup (hbi lenBase spC iW : Word) (Li : Nat)
    (old5 o10 o11 o12 o13 o14 o28 : Word) :
    cpsTripleWithin 15 (C + 72) (C + 132) cvedlCode
      ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) **
        (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ o10) ** (.x11 ↦ᵣ o11) ** (.x12 ↦ᵣ o12) **
        (.x13 ↦ᵣ o13) ** (.x14 ↦ᵣ o14) ** (.x28 ↦ᵣ o28) **
        memOwn IterPtr ** memOwn IterI **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li))
      ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) **
        (.x5 ↦ᵣ IterI) ** (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) **
        (.x12 ↦ᵣ (12 : Word)) ** (.x13 ↦ᵣ COff) ** (.x14 ↦ᵣ CLen) **
        (.x28 ↦ᵣ (lenBase + (iW <<< 3))) **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li)) := by
  -- [18-19] la x5, cvedl_iter_ptr
  have hla18 := la_materialize_within .x5 old5 (C + 72) IterPtr (by decide) (by decide)
    (CodeReq.ofProg_mem_at C (C + 72) cvedlProg 18 (.AUIPC .x5 (EvmAsm.Rv64.laHi (C + 72) IterPtr)) (by bv_omega) (by rw [cvedl_length]; decide) (by decide) (by rw [cvedl_length]; decide))
    (CodeReq.ofProg_mem_at C (C + 76) cvedlProg 19 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (C + 72) IterPtr)) (by bv_omega) (by rw [cvedl_length]; decide) (by decide) (by rw [cvedl_length]; decide))
  -- [20] SD x5 x18 0 : *iter_ptr := hbi
  have s20 := sd_spec_gen_own_within .x5 .x18 IterPtr hbi (0 : BitVec 12) (C + 80)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterPtr + (0 : Word) = IterPtr from by bv_omega] at s20
  have s20' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 80) cvedlProg 20 (.SD .x5 .x18 (0 : BitVec 12)) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s20
  -- [21-22] la x5, cvedl_iter_i
  have hla21 := la_materialize_within .x5 IterPtr (C + 84) IterI (by decide) (by decide)
    (CodeReq.ofProg_mem_at C (C + 84) cvedlProg 21 (.AUIPC .x5 (EvmAsm.Rv64.laHi (C + 84) IterI)) (by bv_omega) (by rw [cvedl_length]; decide) (by decide) (by rw [cvedl_length]; decide))
    (CodeReq.ofProg_mem_at C (C + 88) cvedlProg 22 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (C + 84) IterI)) (by bv_omega) (by rw [cvedl_length]; decide) (by decide) (by rw [cvedl_length]; decide))
  -- [23] SD x5 x21 0 : *iter_i := iW
  have s23 := sd_spec_gen_own_within .x5 .x21 IterI iW (0 : BitVec 12) (C + 92)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterI + (0 : Word) = IterI from by bv_omega] at s23
  have s23' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 92) cvedlProg 23 (.SD .x5 .x21 (0 : BitVec 12)) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s23
  -- [24] SLLI x28 x21 3 : x28 := iW <<< 3
  have s24 := slli_spec_gen_within .x28 .x21 o28 iW (3 : BitVec 6) (C + 96) (by decide)
  rw [show (3 : BitVec 6).toNat = 3 from by decide] at s24
  have s24' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 96) cvedlProg 24 (.SLLI .x28 .x21 (3 : BitVec 6)) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s24
  -- [25] ADD x28 x9 x28 : x28 := lenBase + iW<<<3
  have s25 := add_spec_gen_rd_eq_rs2_within .x28 .x9 lenBase (iW <<< 3) (C + 100) (by decide)
  have s25' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 100) cvedlProg 25 (.ADD .x28 .x9 .x28) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s25
  -- [26] LD x11 x28 0 : x11 := *(lenBase + iW<<<3) = ofNat Li
  have s26 := ld_spec_gen_within .x11 .x28 (lenBase + (iW <<< 3)) o11 (BitVec.ofNat 64 Li)
    (0 : BitVec 12) (C + 104) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (lenBase + (iW <<< 3)) + (0 : Word) = lenBase + (iW <<< 3) from by bv_omega] at s26
  have s26' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 104) cvedlProg 26 (.LD .x11 .x28 (0 : BitVec 12)) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s26
  -- [27] MV x10 x18 : x10 := hbi
  have s27 := mv_spec_gen_within .x10 .x18 hbi o10 (C + 108) (by decide)
  have s27' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 108) cvedlProg 27 (.MV .x10 .x18) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s27
  -- [28] LI x12 12
  have s28 := li_spec_gen_within .x12 o12 (12 : Word) (C + 112) (by decide)
  have s28' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 112) cvedlProg 28 (.LI .x12 (12 : Word)) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s28
  -- [29-30] la x13, cvedl_offset
  have hla29 := la_materialize_within .x13 o13 (C + 116) COff (by decide) (by decide)
    (CodeReq.ofProg_mem_at C (C + 116) cvedlProg 29 (.AUIPC .x13 (EvmAsm.Rv64.laHi (C + 116) COff)) (by bv_omega) (by rw [cvedl_length]; decide) (by decide) (by rw [cvedl_length]; decide))
    (CodeReq.ofProg_mem_at C (C + 120) cvedlProg 30 (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (C + 116) COff)) (by bv_omega) (by rw [cvedl_length]; decide) (by decide) (by rw [cvedl_length]; decide))
  -- [31-32] la x14, cvedl_length
  have hla31 := la_materialize_within .x14 o14 (C + 124) CLen (by decide) (by decide)
    (CodeReq.ofProg_mem_at C (C + 124) cvedlProg 31 (.AUIPC .x14 (EvmAsm.Rv64.laHi (C + 124) CLen)) (by bv_omega) (by rw [cvedl_length]; decide) (by decide) (by rw [cvedl_length]; decide))
    (CodeReq.ofProg_mem_at C (C + 128) cvedlProg 32 (.ADDI .x14 .x14 (EvmAsm.Rv64.laLo (C + 124) CLen)) (by bv_omega) (by rw [cvedl_length]; decide) (by decide) (by rw [cvedl_length]; decide))
  runBlock hla18 s20' hla21 s23' s24' s25' s26' s27' s28' hla29 hla31

#print axioms cvedlSetup

end EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
