/-
  `withdrawalDecode_prog` caller-contract composition (in progress).

  This module hosts the straight-line block lemmas of the 60-instruction
  accessor that bookend the four field decodes:

    * `wdPrologue`  — instructions [0]-[7]: allocate the 32-byte frame, save
      `ra/s0/s1/s2`, and load `s0/s1/s2 := a0/a1/a2` (list ptr / len / output).
    * `wdEpiCore`   — instructions [54]-[59]: restore `ra/s0/s1/s2`, deallocate,
      and return, generic over the callee result footprint `G`.

  Both are stated generic over an untouched frame `G`, exactly like
  `HeaderExtractNumberSpec.epiCore`, so the eventual four-field compose can
  thread its live footprint through them.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.WithdrawalDecodeSpec

namespace EvmAsm.Codegen.WithdrawalDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## Prologue (instructions [0]-[7]) -/

set_option maxRecDepth 8000 in
/-- Allocate the 32-byte frame, save `ra/s0/s1/s2` into the four stack slots,
    and copy the three ABI arguments into the callee-saved registers
    (`s0 := a0 = list ptr`, `s1 := a1 = len`, `s2 := a2 = output ptr`), leaving
    `a0/a1/a2` intact.  Generic over the untouched frame `G`. -/
theorem wdPrologue
    (sp0 spW raIn s0Old s1Old s2Old listBase listLen outBase : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspW : spW = sp0 + signExtend12 (-32 : BitVec 12)) :
    cpsTripleWithin 8 WB (WB + 32) fullCode
      (((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
        (.x18 ↦ᵣ s2Old) ** (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen) **
        (.x12 ↦ᵣ outBase) ** memOwn spW ** memOwn (spW + 8) **
        memOwn (spW + 16) ** memOwn (spW + 24)) ** G)
      (((.x2 ↦ᵣ spW) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLen) **
        (.x18 ↦ᵣ outBase) ** (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen) **
        (.x12 ↦ᵣ outBase) ** (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) **
        ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old)) ** G) := by
  have hz0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hz8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
  have hz16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
  have hz24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
  -- [0] ADDI x2 x2 -32 : sp0 → spW
  have h0 := addi_spec_gen_same_within .x2 sp0 (-32 : BitVec 12) WB (by decide)
  rw [← hspW] at h0
  have h0' := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB WB withdrawalDecode_prog 0
        (.ADDI .x2 .x2 (-32 : BitVec 12)) (by decide) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) h0)
  -- [1] SD x2 x1 0 : store raIn at spW
  have h1 := sd_spec_gen_own_within .x2 .x1 spW raIn (0 : BitVec 12) (WB + 4)
  rw [hz0, show spW + (0 : Word) = spW from by bv_omega] at h1
  have h1' := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 4) withdrawalDecode_prog 1
        (.SD .x2 .x1 (0 : BitVec 12)) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) h1)
  -- [2] SD x2 x8 8 : store s0Old at spW+8
  have h2 := sd_spec_gen_own_within .x2 .x8 spW s0Old (8 : BitVec 12) (WB + 8)
  rw [hz8] at h2
  have h2' := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 8) withdrawalDecode_prog 2
        (.SD .x2 .x8 (8 : BitVec 12)) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) h2)
  -- [3] SD x2 x9 16 : store s1Old at spW+16
  have h3 := sd_spec_gen_own_within .x2 .x9 spW s1Old (16 : BitVec 12) (WB + 12)
  rw [hz16] at h3
  have h3' := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 12) withdrawalDecode_prog 3
        (.SD .x2 .x9 (16 : BitVec 12)) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) h3)
  -- [4] SD x2 x18 24 : store s2Old at spW+24
  have h4 := sd_spec_gen_own_within .x2 .x18 spW s2Old (24 : BitVec 12) (WB + 16)
  rw [hz24] at h4
  have h4' := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 16) withdrawalDecode_prog 4
        (.SD .x2 .x18 (24 : BitVec 12)) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) h4)
  -- [5] MV x8 x10 : x8 := listBase
  have h5 := mv_spec_gen_within .x8 .x10 listBase s0Old (WB + 20) (by decide)
  have h5' := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 20) withdrawalDecode_prog 5 (.MV .x8 .x10)
        (by bv_omega) (by rw [wd_length]; decide) rfl
        (by rw [wd_length]; decide)) h5)
  -- [6] MV x9 x11 : x9 := listLen
  have h6 := mv_spec_gen_within .x9 .x11 listLen s1Old (WB + 24) (by decide)
  have h6' := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 24) withdrawalDecode_prog 6 (.MV .x9 .x11)
        (by bv_omega) (by rw [wd_length]; decide) rfl
        (by rw [wd_length]; decide)) h6)
  -- [7] MV x18 x12 : x18 := outBase
  have h7 := mv_spec_gen_within .x18 .x12 outBase s2Old (WB + 28) (by decide)
  have h7' := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 28) withdrawalDecode_prog 7 (.MV .x18 .x12)
        (by bv_omega) (by rw [wd_length]; decide) rfl
        (by rw [wd_length]; decide)) h7)
  -- Frame each instruction over the untouched local cells.
  have f0 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
     (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ outBase) **
     memOwn spW ** memOwn (spW + 8) ** memOwn (spW + 16) ** memOwn (spW + 24))
    (by pcf) h0'
  have f1 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
     (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ outBase) **
     memOwn (spW + 8) ** memOwn (spW + 16) ** memOwn (spW + 24)) (by pcf) h1'
  have f2 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
     (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ outBase) **
     (spW ↦ₘ raIn) ** memOwn (spW + 16) ** memOwn (spW + 24)) (by pcf) h2'
  have f3 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ s0Old) ** (.x18 ↦ᵣ s2Old) **
     (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ outBase) **
     (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) ** memOwn (spW + 24)) (by pcf) h3'
  have f4 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
     (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ outBase) **
     (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) ** ((spW + 16) ↦ₘ s1Old)) (by pcf) h4'
  have f5 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spW) ** (.x1 ↦ᵣ raIn) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
     (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ outBase) **
     (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) ** ((spW + 16) ↦ₘ s1Old) **
     ((spW + 24) ↦ₘ s2Old)) (by pcf) h5'
  have f6 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spW) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ s2Old) **
     (.x10 ↦ᵣ listBase) ** (.x12 ↦ᵣ outBase) **
     (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) ** ((spW + 16) ↦ₘ s1Old) **
     ((spW + 24) ↦ₘ s2Old)) (by pcf) h6'
  have f7 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spW) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLen) **
     (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen) **
     (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) ** ((spW + 16) ↦ₘ s1Old) **
     ((spW + 24) ↦ₘ s2Old)) (by pcf) h7'
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f0 f1
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 f2
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c012 f3
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0123 f4
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c04 f5
  have c06 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c05 f6
  have c07 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c06 f7
  have hlocal : cpsTripleWithin 8 WB (WB + 32) fullCode
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
        (.x18 ↦ᵣ s2Old) ** (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen) **
        (.x12 ↦ᵣ outBase) ** memOwn spW ** memOwn (spW + 8) **
        memOwn (spW + 16) ** memOwn (spW + 24))
      ((.x2 ↦ᵣ spW) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLen) **
        (.x18 ↦ᵣ outBase) ** (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLen) **
        (.x12 ↦ᵣ outBase) ** (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) **
        ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c07
  have hframed := cpsTripleWithin_frameR G hG hlocal
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hframed

#print axioms wdPrologue

/-! ## Epilogue core (instructions [54]-[59]) -/

set_option maxRecDepth 8000 in
/-- Restore `ra/s0/s1/s2` from the four stack slots, deallocate the 32-byte
    frame, and return.  Generic over the callee result footprint `G`. -/
theorem wdEpiCore
    (sp0 spW raIn s0Old s1Old s2Old x1old x8old x9old x18old : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspW : spW = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 6 (WB + 216) raIn fullCode
      (((.x2 ↦ᵣ spW) ** (.x1 ↦ᵣ x1old) ** (.x8 ↦ᵣ x8old) ** (.x9 ↦ᵣ x9old) **
        (.x18 ↦ᵣ x18old) ** (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) **
        ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old)) ** G)
      (((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
        (.x18 ↦ᵣ s2Old) ** (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) **
        ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old)) ** G) := by
  have hz0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hz8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
  have hz16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
  have hz24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
  -- [54] LD x1 x2 0 : restore ra
  have h0 := ld_spec_gen_within .x1 .x2 spW x1old raIn (0 : BitVec 12) (WB + 216)
    (by decide)
  rw [hz0, show spW + (0 : Word) = spW from by bv_omega] at h0
  have h0' := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 216) withdrawalDecode_prog 54
        (.LD .x1 .x2 (0 : BitVec 12)) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) h0)
  -- [55] LD x8 x2 8 : restore s0
  have h1 := ld_spec_gen_within .x8 .x2 spW x8old s0Old (8 : BitVec 12) (WB + 220)
    (by decide)
  rw [hz8] at h1
  have h1' := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 220) withdrawalDecode_prog 55
        (.LD .x8 .x2 (8 : BitVec 12)) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) h1)
  -- [56] LD x9 x2 16 : restore s1
  have h2 := ld_spec_gen_within .x9 .x2 spW x9old s1Old (16 : BitVec 12) (WB + 224)
    (by decide)
  rw [hz16] at h2
  have h2' := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 224) withdrawalDecode_prog 56
        (.LD .x9 .x2 (16 : BitVec 12)) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) h2)
  -- [57] LD x18 x2 24 : restore s2
  have h3 := ld_spec_gen_within .x18 .x2 spW x18old s2Old (24 : BitVec 12) (WB + 228)
    (by decide)
  rw [hz24] at h3
  have h3' := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 228) withdrawalDecode_prog 57
        (.LD .x18 .x2 (24 : BitVec 12)) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) h3)
  -- [58] ADDI x2 x2 32 : deallocate
  have h4 := addi_spec_gen_same_within .x2 spW (32 : BitVec 12) (WB + 232) (by decide)
  rw [show spW + signExtend12 (32 : BitVec 12) = sp0 from by
    rw [hspW]; exact sext_frameRestore sp0 (-32 : BitVec 12) (32 : BitVec 12)
      (by decide)] at h4
  have h4' := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 232) withdrawalDecode_prog 58
        (.ADDI .x2 .x2 (32 : BitVec 12)) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) h4)
  -- [59] JALR x0 x1 0 : return
  have h5 := EvmAsm.Evm64.ret_spec_within' (WB + 236) raIn
  rw [hret] at h5
  have h5' := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 236) withdrawalDecode_prog 59
        (.JALR .x0 .x1 (0 : BitVec 12)) (by bv_omega) (by rw [wd_length]; decide)
        rfl (by rw [wd_length]; decide)) h5)
  -- Frame each instruction over the untouched local cells.
  have f0 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ x8old) ** (.x9 ↦ᵣ x9old) ** (.x18 ↦ᵣ x18old) **
     ((spW + 8) ↦ₘ s0Old) ** ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old))
    (by pcf) h0'
  have f1 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x9 ↦ᵣ x9old) ** (.x18 ↦ᵣ x18old) **
     (spW ↦ₘ raIn) ** ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old))
    (by pcf) h1'
  have f2 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ s0Old) ** (.x18 ↦ᵣ x18old) **
     (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) ** ((spW + 24) ↦ₘ s2Old))
    (by pcf) h2'
  have f3 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
     (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) ** ((spW + 16) ↦ₘ s1Old))
    (by pcf) h3'
  have f4 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
     (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) ** ((spW + 16) ↦ₘ s1Old) **
     ((spW + 24) ↦ₘ s2Old)) (by pcf) h4'
  have f5 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
     (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) ** ((spW + 16) ↦ₘ s1Old) **
     ((spW + 24) ↦ₘ s2Old)) (by pcf) h5'
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f0 f1
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 f2
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c012 f3
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0123 f4
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c04 f5
  have hlocal : cpsTripleWithin 6 (WB + 216) raIn fullCode
      ((.x2 ↦ᵣ spW) ** (.x1 ↦ᵣ x1old) ** (.x8 ↦ᵣ x8old) ** (.x9 ↦ᵣ x9old) **
        (.x18 ↦ᵣ x18old) ** (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) **
        ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old))
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ s0Old) ** (.x9 ↦ᵣ s1Old) **
        (.x18 ↦ᵣ s2Old) ** (spW ↦ₘ raIn) ** ((spW + 8) ↦ₘ s0Old) **
        ((spW + 16) ↦ₘ s1Old) ** ((spW + 24) ↦ₘ s2Old)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c05
  have hframed := cpsTripleWithin_frameR G hG hlocal
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hframed

#print axioms wdEpiCore

/-! ## Status-return tails ([51]-[52] success, [53] failure) -/

set_option maxRecDepth 8000 in
/-- Success tail [51]-[52]: set `a0 := 0` and jump over the failure store to the
    epilogue entry (`WB+216`).  Generic over the untouched frame `G`. -/
theorem wdSuccessTail (v10old : Word) (G : Assertion) (hG : G.pcFree) :
    cpsTripleWithin 2 (WB + 204) (WB + 216) fullCode
      (((.x10 : Reg) ↦ᵣ v10old) ** G)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** G) := by
  -- [51] LI x10 0
  have h0 := li_spec_gen_within .x10 v10old (0 : Word) (WB + 204) (by decide)
  have h0' := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 204) withdrawalDecode_prog 51
        (.LI .x10 (0 : Word)) (by bv_omega) (by rw [wd_length]; decide) rfl
        (by rw [wd_length]; decide)) h0)
  -- [52] JAL x0 8 : jump to WB+216 (preserves the whole footprint)
  have h1 := jal0_spec_pcFree (P := ((.x10 : Reg) ↦ᵣ (0 : Word)) ** G) (8 : BitVec 21)
    (WB + 208) (pcFree_sepConj pcFree_regIs hG)
  rw [show WB + 208 + signExtend21 (8 : BitVec 21) = WB + 216 from by decide] at h1
  have h1' := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 208) withdrawalDecode_prog 52
        (.JAL .x0 (8 : BitVec 21)) (by bv_omega) (by rw [wd_length]; decide) rfl
        (by rw [wd_length]; decide)) h1)
  have f0 := cpsTripleWithin_frameR G hG h0'
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f0 h1'

#print axioms wdSuccessTail

set_option maxRecDepth 8000 in
/-- Failure tail [53]: set `a0 := 1` and fall through to the epilogue entry
    (`WB+216`).  Generic over the untouched frame `G`. -/
theorem wdFailTail (v10old : Word) (G : Assertion) (hG : G.pcFree) :
    cpsTripleWithin 1 (WB + 212) (WB + 216) fullCode
      (((.x10 : Reg) ↦ᵣ v10old) ** G)
      (((.x10 : Reg) ↦ᵣ (1 : Word)) ** G) := by
  have h0 := li_spec_gen_within .x10 v10old (1 : Word) (WB + 212) (by decide)
  rw [show (WB + 212 : Word) + 4 = WB + 216 from by bv_omega] at h0
  have h0' := cpsTripleWithin_extend_code wd_mono
    (cpsTripleWithin_extend_code (cr' := wdCode)
      (CodeReq.ofProg_mem_at WB (WB + 212) withdrawalDecode_prog 53
        (.LI .x10 (1 : Word)) (by bv_omega) (by rw [wd_length]; decide) rfl
        (by rw [wd_length]; decide)) h0)
  exact cpsTripleWithin_frameR G hG h0'

#print axioms wdFailTail

end EvmAsm.Codegen.WithdrawalDecodeSpec
