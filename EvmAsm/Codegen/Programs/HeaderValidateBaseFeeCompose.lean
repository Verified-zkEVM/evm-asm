/-
  EvmAsm.Codegen.Programs.HeaderValidateBaseFeeCompose

  The machine half of the K74 `header_validate_base_fee` whole-routine spec:
  prologue / K73-call / epilogue / `u256_eq`-call adapters, the two branch
  merges, and the whole-routine `header_validate_base_fee_spec_within` plus
  its non-vacuity witness.  All assertion vocabulary lives in
  `HeaderValidateBaseFeeSpec.lean` (this file's only import of the family).
-/

import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeSpec

namespace EvmAsm.Codegen.HeaderValidateBaseFeeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec
open EvmAsm.Codegen.U256EqSAsm
open EvmAsm.Stateless.SpecRef

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact pcFree_regOwns _
      | exact pcFree_regAtomsOf _ _
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | exact pcFree_frameSlotsOwn _ _
      | apply hvbfBrFrame_pcFree
      | apply hvbfArmFrame_pcFree
      | assumption)
/-! ## §5  The prologue (instructions 0-8) -/

/-- Instructions 0-8: allocate the 16-byte frame, save `ra`/`s0`, shuffle the
    arguments into the K73 calling convention, and materialize
    `a3 = hvbf_expected`. -/
theorem hvbfPrologue
    (sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed : Word)
    (v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5 : Word)
    (hdrFeeBytes parentFeeBytes scratchBytes accBytes : List (BitVec 8))
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-16 : BitVec 12)) :
    cpsTripleWithin 9 K (K + 36) hvbfWholeCode
      (hvbfPre sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
        v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5
        hdrFeeBytes parentFeeBytes scratchBytes accBytes G)
      ((.x1 ↦ᵣ Ret) ** hvbfK73CalleePre spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
          v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5
          hdrFeeBytes parentFeeBytes scratchBytes accBytes G) := by
  have h0 := addi_spec_gen_same_within .x2 sp0 (-16 : BitVec 12) K (by decide)
  rw [← hspC] at h0
  have h0C := cpsTripleWithin_extend_code
    (hvbf_mem 0 (.ADDI .x2 .x2 (-16 : BitVec 12)) K
      (by decide) (by rw [hvbf_length]; decide) rfl) h0
  have h1 := sd_spec_gen_own_within .x2 .x1 spC Ret (0 : BitVec 12) (K + 4)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show spC + (0 : Word) = spC from by bv_omega] at h1
  have h1C := cpsTripleWithin_extend_code
    (hvbf_mem 1 (.SD .x2 .x1 (0 : BitVec 12)) (K + 4)
      (by decide) (by rw [hvbf_length]; decide) rfl) h1
  have h2 := sd_spec_gen_own_within .x2 .x8 spC v8 (8 : BitVec 12) (K + 8)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at h2
  have h2C := cpsTripleWithin_extend_code
    (hvbf_mem 2 (.SD .x2 .x8 (8 : BitVec 12)) (K + 8)
      (by decide) (by rw [hvbf_length]; decide) rfl) h2
  have h3 := mv_spec_gen_within .x8 .x10 hdrFeePtr v8 (K + 12) (by decide)
  have h3C := cpsTripleWithin_extend_code
    (hvbf_mem 3 (.MV .x8 .x10) (K + 12)
      (by decide) (by rw [hvbf_length]; decide) rfl) h3
  have h4 := mv_spec_gen_within .x10 .x11 gasLimit hdrFeePtr (K + 16) (by decide)
  have h4C := cpsTripleWithin_extend_code
    (hvbf_mem 4 (.MV .x10 .x11) (K + 16)
      (by decide) (by rw [hvbf_length]; decide) rfl) h4
  have h5 := mv_spec_gen_within .x11 .x12 gasUsed gasLimit (K + 20) (by decide)
  have h5C := cpsTripleWithin_extend_code
    (hvbf_mem 5 (.MV .x11 .x12) (K + 20)
      (by decide) (by rw [hvbf_length]; decide) rfl) h5
  have h6 := mv_spec_gen_within .x12 .x13 parentFeePtr gasUsed (K + 24) (by decide)
  have h6C := cpsTripleWithin_extend_code
    (hvbf_mem 6 (.MV .x12 .x13) (K + 24)
      (by decide) (by rw [hvbf_length]; decide) rfl) h6
  have hla := la_materialize_within .x13 parentFeePtr (K + 28) hvbfScratchAddr
    (by decide) (by decide)
    (hvbf_mem 7
      (.AUIPC .x13 (Rv64.laHi (K + 28) hvbfScratchAddr)) (K + 28)
      (by decide) (by rw [hvbf_length]; decide) rfl)
    (hvbf_mem 8
      (.ADDI .x13 .x13 (Rv64.laLo (K + 28) hvbfScratchAddr)) (K + 32)
      (by decide) (by rw [hvbf_length]; decide) rfl)
  rw [show (K + 28 : Word) + 8 = K + 36 from by decide] at hla
  have h0F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ Ret) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
      (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ hdrFeePtr) ** (.x11 ↦ᵣ gasLimit) **
      (.x12 ↦ᵣ gasUsed) ** (.x13 ↦ᵣ parentFeePtr) ** regOwns hvbfK73ScratchRegs **
      (.x0 ↦ᵣ (0 : Word)) ** memOwn spC ** memOwn (spC + 8) ** frameSlotsOwn k73Frame spH **
      U256MulU64Be.frameSlots spM f0 f1 f2 f3 f4 f5 ** bytesRegion hdrFeePtr hdrFeeBytes **
      bytesRegion parentFeePtr parentFeeBytes ** bytesRegion hvbfScratchAddr scratchBytes **
      bytesRegion U256MulU64Be.accBase accBytes ** G) (by pcf) h0C
  have h1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
      (.x10 ↦ᵣ hdrFeePtr) ** (.x11 ↦ᵣ gasLimit) ** (.x12 ↦ᵣ gasUsed) **
      (.x13 ↦ᵣ parentFeePtr) ** regOwns hvbfK73ScratchRegs ** (.x0 ↦ᵣ (0 : Word)) **
      memOwn (spC + 8) ** frameSlotsOwn k73Frame spH **
      U256MulU64Be.frameSlots spM f0 f1 f2 f3 f4 f5 ** bytesRegion hdrFeePtr hdrFeeBytes **
      bytesRegion parentFeePtr parentFeeBytes ** bytesRegion hvbfScratchAddr scratchBytes **
      bytesRegion U256MulU64Be.accBase accBytes ** G) (by pcf) h1C
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have h2F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ Ret) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
      (.x10 ↦ᵣ hdrFeePtr) ** (.x11 ↦ᵣ gasLimit) ** (.x12 ↦ᵣ gasUsed) **
      (.x13 ↦ᵣ parentFeePtr) ** regOwns hvbfK73ScratchRegs ** (.x0 ↦ᵣ (0 : Word)) **
      (spC ↦ₘ Ret) ** frameSlotsOwn k73Frame spH **
      U256MulU64Be.frameSlots spM f0 f1 f2 f3 f4 f5 ** bytesRegion hdrFeePtr hdrFeeBytes **
      bytesRegion parentFeePtr parentFeeBytes ** bytesRegion hvbfScratchAddr scratchBytes **
      bytesRegion U256MulU64Be.accBase accBytes ** G) (by pcf) h2C
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 h2F
  have h3F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ Ret) ** (.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
      (.x20 ↦ᵣ v20) ** (.x11 ↦ᵣ gasLimit) ** (.x12 ↦ᵣ gasUsed) ** (.x13 ↦ᵣ parentFeePtr) **
      regOwns hvbfK73ScratchRegs ** (.x0 ↦ᵣ (0 : Word)) **
      (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) ** frameSlotsOwn k73Frame spH **
      U256MulU64Be.frameSlots spM f0 f1 f2 f3 f4 f5 ** bytesRegion hdrFeePtr hdrFeeBytes **
      bytesRegion parentFeePtr parentFeeBytes ** bytesRegion hvbfScratchAddr scratchBytes **
      bytesRegion U256MulU64Be.accBase accBytes ** G) (by pcf) h3C
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 h3F
  have h4F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ Ret) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ hdrFeePtr) **
      (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
      (.x12 ↦ᵣ gasUsed) ** (.x13 ↦ᵣ parentFeePtr) **
      regOwns hvbfK73ScratchRegs ** (.x0 ↦ᵣ (0 : Word)) **
      (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) ** frameSlotsOwn k73Frame spH **
      U256MulU64Be.frameSlots spM f0 f1 f2 f3 f4 f5 ** bytesRegion hdrFeePtr hdrFeeBytes **
      bytesRegion parentFeePtr parentFeeBytes ** bytesRegion hvbfScratchAddr scratchBytes **
      bytesRegion U256MulU64Be.accBase accBytes ** G) (by pcf) h4C
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 h4F
  have h5F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ Ret) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ hdrFeePtr) **
      (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
      (.x10 ↦ᵣ gasLimit) ** (.x13 ↦ᵣ parentFeePtr) **
      regOwns hvbfK73ScratchRegs ** (.x0 ↦ᵣ (0 : Word)) **
      (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) ** frameSlotsOwn k73Frame spH **
      U256MulU64Be.frameSlots spM f0 f1 f2 f3 f4 f5 ** bytesRegion hdrFeePtr hdrFeeBytes **
      bytesRegion parentFeePtr parentFeeBytes ** bytesRegion hvbfScratchAddr scratchBytes **
      bytesRegion U256MulU64Be.accBase accBytes ** G) (by pcf) h5C
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c04 h5F
  have h6F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ Ret) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ hdrFeePtr) **
      (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
      (.x10 ↦ᵣ gasLimit) ** (.x11 ↦ᵣ gasUsed) **
      regOwns hvbfK73ScratchRegs ** (.x0 ↦ᵣ (0 : Word)) **
      (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) ** frameSlotsOwn k73Frame spH **
      U256MulU64Be.frameSlots spM f0 f1 f2 f3 f4 f5 ** bytesRegion hdrFeePtr hdrFeeBytes **
      bytesRegion parentFeePtr parentFeeBytes ** bytesRegion hvbfScratchAddr scratchBytes **
      bytesRegion U256MulU64Be.accBase accBytes ** G) (by pcf) h6C
  have c06 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c05 h6F
  have hlaF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ Ret) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ hdrFeePtr) **
      (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
      (.x10 ↦ᵣ gasLimit) ** (.x11 ↦ᵣ gasUsed) ** (.x12 ↦ᵣ parentFeePtr) **
      regOwns hvbfK73ScratchRegs ** (.x0 ↦ᵣ (0 : Word)) **
      (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) ** frameSlotsOwn k73Frame spH **
      U256MulU64Be.frameSlots spM f0 f1 f2 f3 f4 f5 ** bytesRegion hdrFeePtr hdrFeeBytes **
      bytesRegion parentFeePtr parentFeeBytes ** bytesRegion hvbfScratchAddr scratchBytes **
      bytesRegion U256MulU64Be.accBase accBytes ** G) (by pcf) hla
  have c07 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c06 hlaF
  have hblkW := cpsTripleWithin_extend_code hvbf_mono c07
  refine cpsTripleWithin_weaken ?_ ?_ hblkW
  · intro h hp
    unfold hvbfPre at hp
    xperm_hyp hp
  · intro h hq
    unfold hvbfK73CalleePre
    xperm_hyp hq

/-! ## §6  The K73 call (instruction 9) -/

/-- Instruction 9: `jal ra, eip1559_calc_base_fee_per_gas`, composed with the
    callee contract hypothesis. -/
theorem hvbfK73Call (nK73 : Nat)
    (spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed : Word)
    (v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5 : Word)
    (hdrFeeBytes parentFeeBytes scratchBytes accBytes : List (BitVec 8))
    (G : Assertion) (hG : G.pcFree)
    (hcallee : cpsTripleWithin nK73 K73 (K + 40) wholeCode
      (((.x1 : Reg) ↦ᵣ (K + 40)) **
        hvbfK73CalleePre spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
          v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5
          hdrFeeBytes parentFeeBytes scratchBytes accBytes G)
      (((.x1 : Reg) ↦ᵣ (K + 40)) ** hvbfK73CalleePost spC spH spM Ret hdrFeePtr parentFeePtr
          v8 v9 v18 v19 v20 hdrFeeBytes parentFeeBytes accBytes
          (hvbfExpected gasLimit gasUsed parentFeeBytes) G)) :
    cpsTripleWithin (1 + nK73) (K + 36) (K + 40) hvbfWholeCode
      ((.x1 ↦ᵣ Ret) ** hvbfK73CalleePre spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
          v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5
          hdrFeeBytes parentFeeBytes scratchBytes accBytes G)
      ((.x1 ↦ᵣ (K + 40)) ** hvbfK73CalleePost spC spH spM Ret hdrFeePtr parentFeePtr
          v8 v9 v18 v19 v20 hdrFeeBytes parentFeeBytes accBytes
          (hvbfExpected gasLimit gasUsed parentFeeBytes) G) := by
  have hC := cpsTripleWithin_extend_code k73whole_mono hcallee
  have hcall := callWithin_spec (K + 36) K73 Ret hvbfJalOffK73 nK73
    (by decide)
    (fun a i hi => hvbf_mono a i (hvbf_mem 9 (.JAL .x1 hvbfJalOffK73) (K + 36)
      (by decide) (by rw [hvbf_length]; decide) rfl a i hi))
    (hvbfK73CalleePre_pcFree spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
      v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5
      hdrFeeBytes parentFeeBytes scratchBytes accBytes G hG)
    hC
  rw [show (K + 36 : Word) + 4 = K + 40 from by decide] at hcall
  exact hcall

/-! ## §7  The epilogue (instructions 21-24) -/

/-- Instructions 21-24: reload `ra`/`s0` from the frame, deallocate, and
    return.  The status in `a0` and the frame `F` ride through. -/
theorem hvbfEpilogue (sp0 spC Ret o1 o8 status v8 : Word) (F : Assertion)
    (hF : F.pcFree)
    (hspC : spC = sp0 + signExtend12 (-16 : BitVec 12))
    (hret : Ret &&& ~~~(1 : Word) = Ret) :
    cpsTripleWithin 4 (K + 84) Ret hvbfWholeCode
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x10 ↦ᵣ status) **
        (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) ** F)
      ((.x1 ↦ᵣ Ret) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ v8) ** (.x10 ↦ᵣ status) **
        (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) ** F) := by
  rw [show signExtend12 (-16 : BitVec 12) = (-16 : Word) from by decide] at hspC
  have h84 : cpsTripleWithin 1 (K + 84) (K + 84 + 4)
      (CodeReq.singleton (K + 84) (.LD .x1 .x2 (0 : BitVec 12)))
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** ((spC + signExtend12 (0 : BitVec 12)) ↦ₘ Ret))
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ Ret) ** ((spC + signExtend12 (0 : BitVec 12)) ↦ₘ Ret)) :=
    ld_spec_gen_within .x1 .x2 spC o1 Ret (0 : BitVec 12) (K + 84) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show spC + (0 : Word) = spC from by bv_omega] at h84
  have h88 : cpsTripleWithin 1 (K + 88) (K + 88 + 4)
      (CodeReq.singleton (K + 88) (.LD .x8 .x2 (8 : BitVec 12)))
      ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ o8) ** ((spC + signExtend12 (8 : BitVec 12)) ↦ₘ v8))
      ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ v8) ** ((spC + signExtend12 (8 : BitVec 12)) ↦ₘ v8)) :=
    ld_spec_gen_within .x8 .x2 spC o8 v8 (8 : BitVec 12) (K + 88) (by decide)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at h88
  have h92 : cpsTripleWithin 1 (K + 92) (K + 92 + 4)
      (CodeReq.singleton (K + 92) (.ADDI .x2 .x2 (16 : BitVec 12)))
      (.x2 ↦ᵣ spC) (.x2 ↦ᵣ (spC + signExtend12 (16 : BitVec 12))) :=
    addi_spec_gen_same_within .x2 spC (16 : BitVec 12) (K + 92) (by decide)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
    show spC + (16 : Word) = sp0 from by bv_omega] at h92
  have h84C := cpsTripleWithin_extend_code
    (hvbf_mem 21 (.LD .x1 .x2 (0 : BitVec 12)) (K + 84)
      (by decide) (by rw [hvbf_length]; decide) rfl) h84
  have h88C := cpsTripleWithin_extend_code
    (hvbf_mem 22 (.LD .x8 .x2 (8 : BitVec 12)) (K + 88)
      (by decide) (by rw [hvbf_length]; decide) rfl) h88
  have h92C := cpsTripleWithin_extend_code
    (hvbf_mem 23 (.ADDI .x2 .x2 (16 : BitVec 12)) (K + 92)
      (by decide) (by rw [hvbf_length]; decide) rfl) h92
  have h84F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ o8) ** (.x10 ↦ᵣ status) ** ((spC + 8) ↦ₘ v8) ** F) (by pcf) h84C
  have h88F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ Ret) ** (.x10 ↦ᵣ status) ** (spC ↦ₘ Ret) ** F) (by pcf) h88C
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h84F h88F
  have h92F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ Ret) ** (.x8 ↦ᵣ v8) ** (.x10 ↦ᵣ status) **
      (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) ** F) (by pcf) h92C
  have hblk := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 h92F
  have hjalr := EvmAsm.Evm64.ret_spec_within' (K + 96) Ret
  rw [hret] at hjalr
  have hjalrC := cpsTripleWithin_extend_code
    (hvbf_mem 24 (.JALR .x0 .x1 (0 : BitVec 12)) (K + 96)
      (by decide) (by rw [hvbf_length]; decide) rfl) hjalr
  have hjalrF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ v8) ** (.x10 ↦ᵣ status) **
      (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) ** F) (by pcf) hjalrC
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblk hjalrF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) (cpsTripleWithin_extend_code hvbf_mono hall)

/-! ## §8  The `u256_eq` call (instruction 14) -/

/-- The fixed scratch region is well-formed for any 32-byte content. -/
theorem hvbf_scratch_wf (bs : List (BitVec 8)) (hlen : bs.length = 32) :
    Region.wf ⟨hvbfScratchAddr, bs⟩ := by
  refine ⟨by show hvbfScratchAddr.toNat % 8 = 0; decide,
    by show hvbfScratchAddr.toNat + bs.length < 2 ^ 64; rw [hlen]; decide, ?_⟩
  intro k hk
  rw [hlen] at hk
  show isValidMemAddr (hvbfScratchAddr + BitVec.ofNat 64 k) = true
  interval_cases k <;> decide

/-- Instruction 14: `jal ra, u256_eq`, adapting the general return-form leaf
    spec `u256Eq_spec` to the wrapper's pin-shaped call site.  The peeled
    scratch registers become the flat register file; the header-fee region is
    the leaf's region focus and the scratch region its ambient. -/
theorem hvbfU256EqCall
    (hdrFeePtr : Word) (hdrFeeBytes : List (BitVec 8)) (expected : Nat)
    (F : Assertion) (hF : F.pcFree)
    (hlenHdr : hdrFeeBytes.length = 32)
    (hwfHdr : Region.wf ⟨hdrFeePtr, hdrFeeBytes⟩)
    (hdisj : hdrFeePtr.toNat + 32 ≤ hvbfScratchAddr.toNat ∨
      hvbfScratchAddr.toNat + 32 ≤ hdrFeePtr.toNat) :
    cpsTripleWithin
      (1 + (u256EqBody hdrFeePtr hvbfScratchAddr hdrFeeBytes
        (natToBytesBE 32 expected)).steps)
      (K + 56) (K + 60) hvbfWholeCode
      ((.x1 ↦ᵣ (K + 40)) ** (.x10 ↦ᵣ hdrFeePtr) ** (.x11 ↦ᵣ hvbfScratchAddr) **
        regOwns hvbfEqPeelRegs ** bytesRegion hdrFeePtr hdrFeeBytes **
        bytesRegion hvbfScratchAddr (natToBytesBE 32 expected) ** F)
      ((.x1 ↦ᵣ (K + 60)) ** (.x10 ↦ᵣ (if firstDiff hdrFeeBytes (natToBytesBE 32 expected) 32 = 32
          then (1 : Word) else (0 : Word))) ** regOwns hvbfScratchRegs **
        bytesRegion hdrFeePtr hdrFeeBytes **
        bytesRegion hvbfScratchAddr (natToBytesBE 32 expected) ** F) := by
  have hlenExp : (natToBytesBE 32 expected).length = 32 :=
    natToBytesBE_length 32 expected
  have hwfExp : Region.wf ⟨hvbfScratchAddr, natToBytesBE 32 expected⟩ :=
    hvbf_scratch_wf _ hlenExp
  have hov1 : hdrFeePtr.toNat + 32 < 2 ^ 64 := by
    obtain ⟨_, hov, _⟩ := hwfHdr
    change hdrFeePtr.toNat + hdrFeeBytes.length < 2 ^ 64 at hov
    omega
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns hvbfEqPeelRegs (by decide)
      (P := ((.x1 ↦ᵣ (K + 40)) ** (.x10 ↦ᵣ hdrFeePtr) ** (.x11 ↦ᵣ hvbfScratchAddr) **
        bytesRegion hdrFeePtr hdrFeeBytes **
        bytesRegion hvbfScratchAddr (natToBytesBE 32 expected) ** F))
      (fun vf => ?_))
  -- the flat register file: a0 = header fee ptr, a1 = scratch, rest from vf
  have hpre : u256EqPre hdrFeePtr hvbfScratchAddr hdrFeeBytes
      (natToBytesBE 32 expected)
      (fun r => if r = .x10 then hdrFeePtr else if r = .x11 then hvbfScratchAddr
        else vf r)
      [] (bytesRegion hvbfScratchAddr (natToBytesBE 32 expected)) := by
    refine ⟨?_, ?_, hlenHdr, hlenExp, hov1, by decide, hdisj, rfl⟩
    · show RegFile.get _ .x10 = hdrFeePtr
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x11 = hvbfScratchAddr
      rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl
  have h0 := u256Eq_spec hdrFeePtr hvbfScratchAddr u256EqEntry (K + 60)
    hdrFeeBytes (natToBytesBE 32 expected) (by decide) hwfHdr hwfExp
  rw [u256EqBody_flatten guestLayout] at h0
  -- adapt the asrtM pre/post to the flat pin shape
  have hflat : cpsTripleWithin
      ((u256EqBody hdrFeePtr hvbfScratchAddr hdrFeeBytes
        (natToBytesBE 32 expected)).steps)
      u256EqEntry (K + 60) (CodeReq.ofProg u256EqEntry (u256Eq_prog_of guestLayout))
      (((.x1 : Reg) ↦ᵣ (K + 60)) ** ((.x10 ↦ᵣ hdrFeePtr) ** (.x11 ↦ᵣ hvbfScratchAddr) **
          regAtomsOf vf hvbfEqPeelRegs) **
        bytesRegion hvbfScratchAddr (natToBytesBE 32 expected) **
        bytesRegion hdrFeePtr hdrFeeBytes)
      (((.x1 : Reg) ↦ᵣ (K + 60)) **
        ((.x10 ↦ᵣ (if firstDiff hdrFeeBytes (natToBytesBE 32 expected) 32 = 32
          then (1 : Word) else (0 : Word))) ** regOwns hvbfScratchRegs) **
        bytesRegion hvbfScratchAddr (natToBytesBE 32 expected) **
        bytesRegion hdrFeePtr hdrFeeBytes) := by
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) h0
    · -- flat pre ⊢ (x1 ↦ ret) ** asrtM pre
      have hp1 : ((((.x1 : Reg) ↦ᵣ (K + 60)) **
          (((regFileIs (fun r => if r = .x10 then hdrFeePtr else
                if r = .x11 then hvbfScratchAddr else vf r)) **
              bytesRegion RwRegion.empty.base []) **
            bytesRegion hvbfScratchAddr (natToBytesBE 32 expected))) **
          bytesRegion hdrFeePtr hdrFeeBytes) h := by
        have hx10v : (if (Reg.x10 : Reg) = .x10 then hdrFeePtr else
            if (Reg.x10 : Reg) = .x11 then hvbfScratchAddr else vf .x10) =
            hdrFeePtr := if_pos rfl
        have hx11v : (if (Reg.x11 : Reg) = .x10 then hdrFeePtr else
            if (Reg.x11 : Reg) = .x11 then hvbfScratchAddr else vf .x11) =
            hvbfScratchAddr := by
          rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
          exact if_pos rfl
        have hcongr : regAtomsOf (fun r => if r = .x10 then hdrFeePtr else
              if r = .x11 then hvbfScratchAddr else vf r) hvbfEqPeelRegs =
            regAtomsOf vf hvbfEqPeelRegs :=
          regAtomsOf_congr _ vf hvbfEqPeelRegs (fun r hr => by
            show (if r = .x10 then hdrFeePtr else
                if r = .x11 then hvbfScratchAddr else vf r) = vf r
            rw [if_neg (fun (hc : r = .x10) => hvbf_x10_notin_peel (hc ▸ hr)),
              if_neg (fun (hc : r = .x11) => hvbf_x11_notin_peel (hc ▸ hr))])
        rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
          bytesRegion_nil, sepConj_emp_right', hvbf_exposedRegs_split, hx10v, hx11v,
          hcongr]
        xperm_hyp hp
      have hintro : ∀ hp', (((.x1 : Reg) ↦ᵣ (K + 60)) **
          (((regFileIs (fun r => if r = .x10 then hdrFeePtr else
                if r = .x11 then hvbfScratchAddr else vf r)) **
              bytesRegion RwRegion.empty.base []) **
            bytesRegion hvbfScratchAddr (natToBytesBE 32 expected))) hp' →
          (((.x1 : Reg) ↦ᵣ (K + 60)) ** asrtOf RwRegion.empty
              (u256EqPre hdrFeePtr hvbfScratchAddr hdrFeeBytes
                (natToBytesBE 32 expected))) hp' :=
        sepConj_mono_right (asrtOf_intro_ambient RwRegion.empty
          (u256EqPre hdrFeePtr hvbfScratchAddr hdrFeeBytes
            (natToBytesBE 32 expected))
          (fun r => if r = .x10 then hdrFeePtr else
            if r = .x11 then hvbfScratchAddr else vf r)
          [] (bytesRegion hvbfScratchAddr (natToBytesBE 32 expected))
          rfl (bytesRegion_pcFree _ _) hpre)
      have hp2 := sepConj_mono_left hintro h hp1
      show (((.x1 : Reg) ↦ᵣ (K + 60)) ** asrtM (Region.mk hdrFeePtr hdrFeeBytes) RwRegion.empty
          (u256EqPre hdrFeePtr hvbfScratchAddr hdrFeeBytes
            (natToBytesBE 32 expected))) h
      unfold asrtM
      xperm_hyp hp2
    · -- (x1 ↦ ret) ** asrtM post ⊢ flat post
      unfold asrtM at hq
      have hq1 : ((((.x1 : Reg) ↦ᵣ (K + 60)) ** asrtOf RwRegion.empty
            (u256EqPost hdrFeePtr hvbfScratchAddr hdrFeeBytes
              (natToBytesBE 32 expected))) ** bytesRegion hdrFeePtr hdrFeeBytes) h := by
        xperm_hyp hq
      have hq2 := sepConj_mono_left (sepConj_mono_right
        (asrtOf_elim_ambient RwRegion.empty
          (u256EqPost hdrFeePtr hvbfScratchAddr hdrFeeBytes
            (natToBytesBE 32 expected))
          (bytesRegion hvbfScratchAddr (natToBytesBE 32 expected))
          (fun _ _ _ hpost => hpost.2.2.2.2.2)
          (fun rf' ws' hlen hpost hp hh => by
            obtain rfl := List.eq_nil_of_length_eq_zero hlen
            rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
              bytesRegion_nil, sepConj_emp_right'] at hh
            have hx10 : rf' .x10 =
                (if firstDiff hdrFeeBytes (natToBytesBE 32 expected) 32 = 32
          then (1 : Word) else (0 : Word)) := by
              have h1 := hpost.1
              rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)] at h1
              exact h1
            rw [hvbf_exposedRegs_split_post, hx10] at hh
            exact sepConj_mono_left
              (sepConj_mono_right (regAtomsOf_to_regOwns _ _)) hp hh))) h hq1
      xperm_hyp hq2
  -- extend into the union and compose the JAL
  have h0C := cpsTripleWithin_extend_code u256eq_mono hflat
  have hcall := callWithin_spec (K + 56) u256EqEntry (K + 40) hvbfJalOffEq
    ((u256EqBody hdrFeePtr hvbfScratchAddr hdrFeeBytes
        (natToBytesBE 32 expected)).steps)
    (by decide)
    (fun a i hi => hvbf_mono a i (hvbf_mem 14 (.JAL .x1 hvbfJalOffEq) (K + 56)
      (by decide) (by rw [hvbf_length]; decide) rfl a i hi))
    (by pcf)
    h0C
  rw [show (K + 56 : Word) + 4 = K + 60 from by decide] at hcall
  have hcallF := cpsTripleWithin_frameR F hF hcall
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [hvbfEqPeelRegs, regAtomsOf_cons, regAtomsOf_nil,
        sepConj_emp_right'] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hcallF

/-- The dispatch frame at the post-K73 BNE: everything but the compared
    `a0`/`x0`. -/
def hvbfBrFrame (spC spH spM Ret hdrFeePtr parentFeePtr : Word)
    (v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 : Word)
    (hdrFeeBytes parentFeeBytes outBytes accBytes : List (BitVec 8))
    (G : Assertion) : Assertion :=
  (.x1 ↦ᵣ (K + 40)) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ hdrFeePtr) **
  (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
  regOwns hvbfScratchRegs **
  frameSlotsSaved k73Frame spH (k73Saved (K + 40) hdrFeePtr v9 v18 v19 v20) **
  U256MulU64Be.frameSlots spM g0 g1 g2 g3 g4 g5 **
  bytesRegion parentFeePtr parentFeeBytes ** bytesRegion hvbfScratchAddr outBytes **
  bytesRegion U256MulU64Be.accBase accBytes **
  (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) ** bytesRegion hdrFeePtr hdrFeeBytes ** G

/-- The status-arm frame: the owned scratch registers and all memory except
    the wrapper's frame cells and the epilogue registers. -/
def hvbfArmFrame (spH spM hdrFeePtr parentFeePtr : Word)
    (v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 : Word)
    (hdrFeeBytes parentFeeBytes outBytes accBytes : List (BitVec 8))
    (G : Assertion) : Assertion :=
  regOwns hvbfScratchRegs **
  (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
  frameSlotsSaved k73Frame spH (k73Saved (K + 40) hdrFeePtr v9 v18 v19 v20) **
  U256MulU64Be.frameSlots spM g0 g1 g2 g3 g4 g5 **
  bytesRegion hdrFeePtr hdrFeeBytes ** bytesRegion parentFeePtr parentFeeBytes **
  bytesRegion hvbfScratchAddr outBytes **
  bytesRegion U256MulU64Be.accBase accBytes ** G

theorem hvbfBrFrame_pcFree (spC spH spM Ret hdrFeePtr parentFeePtr : Word)
    (v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 : Word)
    (hdrFeeBytes parentFeeBytes outBytes accBytes : List (BitVec 8))
    (G : Assertion) (hG : G.pcFree) :
    (hvbfBrFrame spC spH spM Ret hdrFeePtr parentFeePtr
      v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5
      hdrFeeBytes parentFeeBytes outBytes accBytes G).pcFree := by
  unfold hvbfBrFrame U256MulU64Be.frameSlots
  pcf

theorem hvbfArmFrame_pcFree (spH spM hdrFeePtr parentFeePtr : Word)
    (v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 : Word)
    (hdrFeeBytes parentFeeBytes outBytes accBytes : List (BitVec 8))
    (G : Assertion) (hG : G.pcFree) :
    (hvbfArmFrame spH spM hdrFeePtr parentFeePtr
      v9 v18 v19 v20 g0 g1 g2 g3 g4 g5
      hdrFeeBytes parentFeeBytes outBytes accBytes G).pcFree := by
  unfold hvbfArmFrame U256MulU64Be.frameSlots
  pcf

/-! ## §9  The `beq` status select (instructions 15-19 + epilogue) -/

/-- The frame carried across the `beq` at K+60: everything but the compared
    registers `a0`/`x0`. -/
def hvbfEqFrame (spC spH spM Ret hdrFeePtr parentFeePtr : Word)
    (v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 : Word)
    (hdrFeeBytes parentFeeBytes accBytes : List (BitVec 8)) (expected : Nat)
    (G : Assertion) : Assertion :=
  (.x1 ↦ᵣ (K + 60)) ** regOwns hvbfScratchRegs **
  (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ hdrFeePtr) **
  (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
  (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) **
  frameSlotsSaved k73Frame spH (k73Saved (K + 40) hdrFeePtr v9 v18 v19 v20) **
  U256MulU64Be.frameSlots spM g0 g1 g2 g3 g4 g5 **
  bytesRegion hdrFeePtr hdrFeeBytes **
  bytesRegion parentFeePtr parentFeeBytes **
  bytesRegion hvbfScratchAddr (natToBytesBE 32 expected) **
  bytesRegion U256MulU64Be.accBase accBytes ** G

theorem hvbfEqFrame_pcFree (spC spH spM Ret hdrFeePtr parentFeePtr : Word)
    (v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 : Word)
    (hdrFeeBytes parentFeeBytes accBytes : List (BitVec 8)) (expected : Nat)
    (G : Assertion) (hG : G.pcFree) :
    (hvbfEqFrame spC spH spM Ret hdrFeePtr parentFeePtr
      v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5
      hdrFeeBytes parentFeeBytes accBytes expected G).pcFree := by
  unfold hvbfEqFrame U256MulU64Be.frameSlots
  pcf

/-- A status arm: `LI a0, status` at `liPc`, an unconditional jump at `jalPc`
    into the epilogue at K+84, and the epilogue itself.  6 steps. -/
theorem hvbfStatusArm (status v10 : Word) (liPc jalPc : Word) (joff : BitVec 21)
    (sp0 spC Ret o1 o8 v8 : Word) (F : Assertion) (hF : F.pcFree)
    (hspC : spC = sp0 + signExtend12 (-16 : BitVec 12))
    (hret : Ret &&& ~~~(1 : Word) = Ret)
    (hlij : liPc + 4 = jalPc)
    (hjale : jalPc + signExtend21 joff = K + 84)
    (hmemLI : ∀ a i, CodeReq.singleton liPc (.LI .x10 status) a = some i →
      hvbfWholeCode a = some i)
    (hmemJAL : ∀ a i, CodeReq.singleton jalPc (.JAL .x0 joff) a = some i →
      hvbfWholeCode a = some i) :
    cpsTripleWithin 6 liPc Ret hvbfWholeCode
      (((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word))) ** ((.x1 ↦ᵣ o1) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ o8) **
          (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) ** F))
      ((.x1 ↦ᵣ Ret) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ v8) ** (.x10 ↦ᵣ status) **
        (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) ** ((.x0 ↦ᵣ (0 : Word)) ** F)) := by
  have hli := li_spec_gen_within .x10 v10 status liPc (by decide)
  rw [hlij] at hli
  have hliC := cpsTripleWithin_extend_code hmemLI hli
  have hliF := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** ((.x1 ↦ᵣ o1) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ o8) **
        (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) ** F)) (by pcf) hliC
  have hjal := jal_x0_spec_gen_within joff jalPc
  rw [hjale] at hjal
  have hjalC := cpsTripleWithin_extend_code hmemJAL hjal
  have hjalF : cpsTripleWithin 1 jalPc (K + 84) hvbfWholeCode
      (((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** ((.x1 ↦ᵣ o1) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ o8) **
          (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) ** F)))
      (((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** ((.x1 ↦ᵣ o1) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ o8) **
          (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) ** F))) := by
    have h0 := cpsTripleWithin_frameR
      (((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** ((.x1 ↦ᵣ o1) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ o8) **
          (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) ** F))) (by pcf) hjalC
    exact cpsTripleWithin_weaken
      (fun _ hp => (sepConj_emp_left _).2 hp)
      (fun _ hq => (sepConj_emp_left _).1 hq) h0
  have hs1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hliF hjalF
  have hep := hvbfEpilogue sp0 spC Ret o1 o8 status v8 ((.x0 ↦ᵣ (0 : Word)) ** F)
    (by pcf) hspC hret
  have hs2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hs1 hep
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hs2

/-- Instructions 15-19 plus the shared epilogue: the `beq` at K+60 splits the
    `u256_eq` result into the status-0 arm (full match, not taken) and the
    status-1 arm (mismatch, taken); both jump to the epilogue and return. -/
theorem hvbfEqDispatch
    (sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed : Word)
    (v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 : Word)
    (hdrFeeBytes parentFeeBytes accBytes : List (BitVec 8))
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-16 : BitVec 12))
    (hret : Ret &&& ~~~(1 : Word) = Ret)
    (hlenHdr : hdrFeeBytes.length = 32) :
    cpsTripleWithin 7 (K + 60) Ret hvbfWholeCode
      (((.x10 ↦ᵣ (if firstDiff hdrFeeBytes
            (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes)) 32 = 32
          then (1 : Word) else (0 : Word))) ** (.x0 ↦ᵣ (0 : Word))) **
        hvbfEqFrame spC spH spM Ret hdrFeePtr parentFeePtr
          v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 hdrFeeBytes parentFeeBytes accBytes
          (hvbfExpected gasLimit gasUsed parentFeeBytes) G)
      (hvbfEqPost sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
        v8 v9 v18 v19 v20 hdrFeeBytes parentFeeBytes accBytes G) := by
  have hlenExp : (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes)).length
      = 32 := natToBytesBE_length 32 _
  have hbeq := beq_spec_gen_within .x10 .x0 (12 : BitVec 13)
    (if firstDiff hdrFeeBytes
        (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes)) 32 = 32
      then (1 : Word) else (0 : Word)) (0 : Word) (K + 60)
  rw [show (K + 60 : Word) + 4 = K + 64 from by decide,
    show (K + 60 : Word) + signExtend13 (12 : BitVec 13) = K + 72 from by decide] at hbeq
  have hbeqC := cpsBranchWithin_extend_code
    (fun a i hi => hvbf_mono a i (hvbf_mem 15 (.BEQ .x10 .x0 (12 : BitVec 13)) (K + 60)
      (by decide) (by rw [hvbf_length]; decide) rfl a i hi)) hbeq
  have hbeqF := cpsBranchWithin_frameR
    (hvbfEqFrame spC spH spM Ret hdrFeePtr parentFeePtr
      v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 hdrFeeBytes parentFeeBytes accBytes
      (hvbfExpected gasLimit gasUsed parentFeeBytes) G)
    (hvbfEqFrame_pcFree spC spH spM Ret hdrFeePtr parentFeePtr
      v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 hdrFeeBytes parentFeeBytes accBytes
      (hvbfExpected gasLimit gasUsed parentFeeBytes) G hG) hbeqC
  -- match arm (not taken: u256_eq returned 1, all 32 bytes agree)
  have hmatchCont : cpsTripleWithin 6 (K + 64) Ret hvbfWholeCode
      (((.x10 ↦ᵣ (if firstDiff hdrFeeBytes
            (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes)) 32 = 32
          then (1 : Word) else (0 : Word))) ** ((.x0 ↦ᵣ (0 : Word)) ** ⌜(if firstDiff hdrFeeBytes
              (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes)) 32 = 32
            then (1 : Word) else (0 : Word)) ≠ (0 : Word)⌝)) **
        hvbfEqFrame spC spH spM Ret hdrFeePtr parentFeePtr
          v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 hdrFeeBytes parentFeeBytes accBytes
          (hvbfExpected gasLimit gasUsed parentFeeBytes) G)
      (hvbfEqPost sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
        v8 v9 v18 v19 v20 hdrFeeBytes parentFeeBytes accBytes G) := by
    refine cpsTripleWithin_weaken hvbf_pure_pull_branch (fun h hq => hq)
      (cpsTripleWithin_pure_pre (fun hne => ?_))
    have hfd : firstDiff hdrFeeBytes
        (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes)) 32 = 32 := by
      by_contra hfd
      exact hne (if_neg hfd)
    have hmatch : hdrFeeBytes =
        natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes) :=
      hvbf_eq_of_firstDiff_eq hlenHdr hlenExp hfd
    have harm := hvbfStatusArm (0 : Word)
      (if firstDiff hdrFeeBytes
          (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes)) 32 = 32
        then (1 : Word) else (0 : Word))
      (K + 64) (K + 68) (16 : BitVec 21) sp0 spC Ret (K + 60) hdrFeePtr v8
      (regOwns hvbfScratchRegs **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame spH (k73Saved (K + 40) hdrFeePtr v9 v18 v19 v20) **
        U256MulU64Be.frameSlots spM g0 g1 g2 g3 g4 g5 ** bytesRegion hdrFeePtr hdrFeeBytes **
        bytesRegion parentFeePtr parentFeeBytes ** bytesRegion hvbfScratchAddr
          (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes)) **
        bytesRegion U256MulU64Be.accBase accBytes ** G)
      (by pcf) hspC hret (by decide) (by decide)
      (fun a i hi => hvbf_mono a i (hvbf_mem 16 (.LI .x10 (0 : Word)) (K + 64)
        (by decide) (by rw [hvbf_length]; decide) rfl a i hi))
      (fun a i hi => hvbf_mono a i (hvbf_mem 17 (.JAL .x0 (16 : BitVec 21)) (K + 68)
        (by decide) (by rw [hvbf_length]; decide) rfl a i hi))
    refine cpsTripleWithin_weaken
      (fun h hp => by unfold hvbfEqFrame at hp; xperm_hyp hp) (fun h hq => ?_) harm
    unfold hvbfEqPost hvbfRetMatchPost
    refine Or.inl ?_
    refine ⟨g0, g1, g2, g3, g4, g5, ?_⟩
    refine (sepConj_pure_right _).2 ⟨?_, hmatch, ?_⟩
    · unfold hvbfRetMatchState hvbfRetCommon
      xperm_hyp hq
    · intro bl hb
      exact hvbfSpecRefBaseFeeCheck_ok bl gasLimit gasUsed parentFeeBytes hdrFeeBytes
        hb hmatch
  -- mismatch arm (taken: u256_eq returned 0, some byte differs)
  have hmismatchCont : cpsTripleWithin 6 (K + 72) Ret hvbfWholeCode
      (((.x10 ↦ᵣ (if firstDiff hdrFeeBytes
            (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes)) 32 = 32
          then (1 : Word) else (0 : Word))) ** ((.x0 ↦ᵣ (0 : Word)) ** ⌜(if firstDiff hdrFeeBytes
              (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes)) 32 = 32
            then (1 : Word) else (0 : Word)) = (0 : Word)⌝)) **
        hvbfEqFrame spC spH spM Ret hdrFeePtr parentFeePtr
          v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 hdrFeeBytes parentFeeBytes accBytes
          (hvbfExpected gasLimit gasUsed parentFeeBytes) G)
      (hvbfEqPost sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
        v8 v9 v18 v19 v20 hdrFeeBytes parentFeeBytes accBytes G) := by
    refine cpsTripleWithin_weaken hvbf_pure_pull_branch (fun h hq => hq)
      (cpsTripleWithin_pure_pre (fun heq => ?_))
    have hfd : firstDiff hdrFeeBytes
        (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes)) 32 ≠ 32 := by
      intro h32
      rw [if_pos h32] at heq
      exact absurd heq (by decide)
    have hneB : hdrFeeBytes ≠
        natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes) :=
      hvbf_ne_of_firstDiff_ne hfd
    have harm := hvbfStatusArm (1 : Word)
      (if firstDiff hdrFeeBytes
          (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes)) 32 = 32
        then (1 : Word) else (0 : Word))
      (K + 72) (K + 76) (8 : BitVec 21) sp0 spC Ret (K + 60) hdrFeePtr v8
      (regOwns hvbfScratchRegs **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame spH (k73Saved (K + 40) hdrFeePtr v9 v18 v19 v20) **
        U256MulU64Be.frameSlots spM g0 g1 g2 g3 g4 g5 ** bytesRegion hdrFeePtr hdrFeeBytes **
        bytesRegion parentFeePtr parentFeeBytes ** bytesRegion hvbfScratchAddr
          (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes)) **
        bytesRegion U256MulU64Be.accBase accBytes ** G)
      (by pcf) hspC hret (by decide) (by decide)
      (fun a i hi => hvbf_mono a i (hvbf_mem 18 (.LI .x10 (1 : Word)) (K + 72)
        (by decide) (by rw [hvbf_length]; decide) rfl a i hi))
      (fun a i hi => hvbf_mono a i (hvbf_mem 19 (.JAL .x0 (8 : BitVec 21)) (K + 76)
        (by decide) (by rw [hvbf_length]; decide) rfl a i hi))
    refine cpsTripleWithin_weaken
      (fun h hp => by unfold hvbfEqFrame at hp; xperm_hyp hp) (fun h hq => ?_) harm
    unfold hvbfEqPost hvbfRetMismatchPost
    refine Or.inr ?_
    refine ⟨g0, g1, g2, g3, g4, g5, ?_⟩
    refine (sepConj_pure_right _).2 ⟨?_, hneB, ?_⟩
    · unfold hvbfRetMismatchState hvbfRetCommon
      xperm_hyp hq
    · intro bl hb
      exact hvbfSpecRefBaseFeeCheck_mismatch bl gasLimit gasUsed parentFeeBytes
        hdrFeeBytes hb hneB
  exact cpsBranchWithin_merge_same_cr
    (cpsBranchWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hq => hq) (fun h hq => hq) hbeqF)
    hmismatchCont hmatchCont

/-! ## §10  The K73-success path (instructions 11-14 + the `beq` select) -/

/-- Instructions 11-14 on the K73-success path: `MV a0, s0` (the header fee
    pointer), `la a1, hvbf_expected`, and the `u256_eq` call; then the `beq`
    select.  The pre is the BNE not-taken state with the scratch region
    already rewritten to the expected encoding (the `status = 0` case of the
    callee post's relation). -/
theorem hvbfSuccessCont
    (sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed : Word)
    (v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 : Word)
    (hdrFeeBytes parentFeeBytes accBytes : List (BitVec 8))
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-16 : BitVec 12))
    (hret : Ret &&& ~~~(1 : Word) = Ret)
    (hlenHdr : hdrFeeBytes.length = 32)
    (hwfHdr : Region.wf ⟨hdrFeePtr, hdrFeeBytes⟩)
    (hdisjHdrScr : hdrFeePtr.toNat + 32 ≤ hvbfScratchAddr.toNat ∨
      hvbfScratchAddr.toNat + 32 ≤ hdrFeePtr.toNat) :
    cpsTripleWithin
      (11 + (u256EqBody hdrFeePtr hvbfScratchAddr hdrFeeBytes
        (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes))).steps)
      (K + 44) Ret hvbfWholeCode
      (((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x1 ↦ᵣ (K + 40)) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ hdrFeePtr) **
          (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
          regOwns hvbfScratchRegs **
          frameSlotsSaved k73Frame spH (k73Saved (K + 40) hdrFeePtr v9 v18 v19 v20) **
          U256MulU64Be.frameSlots spM g0 g1 g2 g3 g4 g5 **
          bytesRegion parentFeePtr parentFeeBytes ** bytesRegion hvbfScratchAddr
            (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes)) **
          bytesRegion U256MulU64Be.accBase accBytes ** (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) **
          bytesRegion hdrFeePtr hdrFeeBytes ** G))
      (hvbfEqPost sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
        v8 v9 v18 v19 v20 hdrFeeBytes parentFeeBytes accBytes G) := by
  -- instruction 11: MV a0, s0
  have hmv := mv_spec_gen_within .x10 .x8 hdrFeePtr (0 : Word) (K + 44) (by decide)
  rw [show (K + 44 : Word) + 4 = K + 48 from by decide] at hmv
  have hmvC := cpsTripleWithin_extend_code
    (fun a i hi => hvbf_mono a i (hvbf_mem 11 (.MV .x10 .x8) (K + 44)
      (by decide) (by rw [hvbf_length]; decide) rfl a i hi)) hmv
  have hmvF := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** ((.x1 ↦ᵣ (K + 40)) ** (.x2 ↦ᵣ spC) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        regOwns hvbfScratchRegs **
        frameSlotsSaved k73Frame spH (k73Saved (K + 40) hdrFeePtr v9 v18 v19 v20) **
        U256MulU64Be.frameSlots spM g0 g1 g2 g3 g4 g5 **
        bytesRegion parentFeePtr parentFeeBytes ** bytesRegion hvbfScratchAddr
          (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes)) **
        bytesRegion U256MulU64Be.accBase accBytes ** (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) **
        bytesRegion hdrFeePtr hdrFeeBytes ** G)) (by pcf) hmvC
  -- instructions 12-13: la a1, hvbf_expected (a1 is only owned after K73)
  have hla : ∀ v11 : Word, cpsTripleWithin 2 (K + 48) (K + 56) hvbfWholeCode
      (((.x10 ↦ᵣ hdrFeePtr) ** (.x8 ↦ᵣ hdrFeePtr) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwns hvbfEqPeelRegs ** (.x1 ↦ᵣ (K + 40)) ** (.x2 ↦ᵣ spC) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame spH (k73Saved (K + 40) hdrFeePtr v9 v18 v19 v20) **
        U256MulU64Be.frameSlots spM g0 g1 g2 g3 g4 g5 **
        bytesRegion parentFeePtr parentFeeBytes ** bytesRegion hvbfScratchAddr
          (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes)) **
        bytesRegion U256MulU64Be.accBase accBytes ** (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) **
        bytesRegion hdrFeePtr hdrFeeBytes ** G) ** ((.x11 : Reg) ↦ᵣ v11))
      (((.x10 ↦ᵣ hdrFeePtr) ** (.x8 ↦ᵣ hdrFeePtr) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwns hvbfEqPeelRegs ** (.x1 ↦ᵣ (K + 40)) ** (.x2 ↦ᵣ spC) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame spH (k73Saved (K + 40) hdrFeePtr v9 v18 v19 v20) **
        U256MulU64Be.frameSlots spM g0 g1 g2 g3 g4 g5 **
        bytesRegion parentFeePtr parentFeeBytes ** bytesRegion hvbfScratchAddr
          (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes)) **
        bytesRegion U256MulU64Be.accBase accBytes ** (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) **
        bytesRegion hdrFeePtr hdrFeeBytes ** G) ** ((.x11 : Reg) ↦ᵣ hvbfScratchAddr)) := by
    intro v11
    have hla0 := la_materialize_within .x11 v11 (K + 48) hvbfScratchAddr
      (by decide) (by decide)
      (fun a i hi => hvbf_mono a i (hvbf_mem 12
        (.AUIPC .x11 (Rv64.laHi (K + 48) hvbfScratchAddr)) (K + 48)
        (by decide) (by rw [hvbf_length]; decide) rfl a i hi))
      (fun a i hi => hvbf_mono a i (hvbf_mem 13
        (.ADDI .x11 .x11 (Rv64.laLo (K + 48) hvbfScratchAddr)) (K + 52)
        (by decide) (by rw [hvbf_length]; decide) rfl a i hi))
    rw [show (K + 48 : Word) + 8 = K + 56 from by decide] at hla0
    have hla1 := cpsTripleWithin_frameR
      (((.x10 ↦ᵣ hdrFeePtr) ** (.x8 ↦ᵣ hdrFeePtr) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwns hvbfEqPeelRegs ** (.x1 ↦ᵣ (K + 40)) ** (.x2 ↦ᵣ spC) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame spH (k73Saved (K + 40) hdrFeePtr v9 v18 v19 v20) **
        U256MulU64Be.frameSlots spM g0 g1 g2 g3 g4 g5 **
        bytesRegion parentFeePtr parentFeeBytes ** bytesRegion hvbfScratchAddr
          (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes)) **
        bytesRegion U256MulU64Be.accBase accBytes ** (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) **
        bytesRegion hdrFeePtr hdrFeeBytes ** G)) (by pcf) hla0
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hla1
  have hla' := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x11) hla
  have hs1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [hvbfScratchRegs, regOwns_cons] at hp
      xperm_hyp hp)
    hmvF hla'
  -- instruction 14: the u256_eq call
  have heq := hvbfU256EqCall hdrFeePtr hdrFeeBytes
    (hvbfExpected gasLimit gasUsed parentFeeBytes)
    ((.x0 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ hdrFeePtr) **
      (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
      frameSlotsSaved k73Frame spH (k73Saved (K + 40) hdrFeePtr v9 v18 v19 v20) **
      U256MulU64Be.frameSlots spM g0 g1 g2 g3 g4 g5 ** bytesRegion parentFeePtr parentFeeBytes **
      bytesRegion U256MulU64Be.accBase accBytes ** (spC ↦ₘ Ret) ** ((spC + 8) ↦ₘ v8) ** G)
    (by pcf) hlenHdr hwfHdr hdisjHdrScr
  have hs2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hs1 heq
  -- instruction 15+: the beq select
  have hdis := hvbfEqDispatch sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
    v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 hdrFeeBytes parentFeeBytes accBytes G hG
    hspC hret hlenHdr
  have hs3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by unfold hvbfEqFrame; xperm_hyp hp) hs2 hdis
  refine cpsTripleWithin_mono_nSteps ?_ (cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp) (fun h hq => hq) hs3)
  omega

/-! ## §11  The post-K73 dispatch (instruction 10) -/

/-- Instruction 10 (`bne a0, x0, K+80`) and everything after it: the K73
    failure arm (status 2) and the success path merge into the three-way
    return postcondition. -/
theorem hvbfDispatch
    (sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed : Word)
    (v8 v9 v18 v19 v20 : Word)
    (hdrFeeBytes parentFeeBytes accBytes : List (BitVec 8))
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-16 : BitVec 12))
    (hret : Ret &&& ~~~(1 : Word) = Ret)
    (hlenHdr : hdrFeeBytes.length = 32)
    (hwfHdr : Region.wf ⟨hdrFeePtr, hdrFeeBytes⟩)
    (hdisjHdrScr : hdrFeePtr.toNat + 32 ≤ hvbfScratchAddr.toNat ∨
      hvbfScratchAddr.toNat + 32 ≤ hdrFeePtr.toNat) :
    cpsTripleWithin
      (12 + (u256EqBody hdrFeePtr hvbfScratchAddr hdrFeeBytes
        (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes))).steps)
      (K + 40) Ret hvbfWholeCode
      ((.x1 ↦ᵣ (K + 40)) ** hvbfK73CalleePost spC spH spM Ret hdrFeePtr parentFeePtr
          v8 v9 v18 v19 v20 hdrFeeBytes parentFeeBytes accBytes
          (hvbfExpected gasLimit gasUsed parentFeeBytes) G)
      (hvbfRetPost sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
        v8 v9 v18 v19 v20 hdrFeeBytes parentFeeBytes accBytes G) := by
  -- pull the callee post's existentials and its pure relation
  refine cpsTripleWithin_weaken (fun h hp => hvbf_sepConj_exists_right _ _ _ hp)
    (fun h hq => hq) (cpsTripleWithin_exists_pre_gen (fun status => ?_))
  refine cpsTripleWithin_weaken (fun h hp => hvbf_sepConj_exists_right _ _ _ hp)
    (fun h hq => hq) (cpsTripleWithin_exists_pre_gen (fun outBytes => ?_))
  refine cpsTripleWithin_weaken (fun h hp => hvbf_sepConj_exists_right _ _ _ hp)
    (fun h hq => hq) (cpsTripleWithin_exists_pre_gen (fun g0 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => hvbf_sepConj_exists_right _ _ _ hp)
    (fun h hq => hq) (cpsTripleWithin_exists_pre_gen (fun g1 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => hvbf_sepConj_exists_right _ _ _ hp)
    (fun h hq => hq) (cpsTripleWithin_exists_pre_gen (fun g2 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => hvbf_sepConj_exists_right _ _ _ hp)
    (fun h hq => hq) (cpsTripleWithin_exists_pre_gen (fun g3 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => hvbf_sepConj_exists_right _ _ _ hp)
    (fun h hq => hq) (cpsTripleWithin_exists_pre_gen (fun g4 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => hvbf_sepConj_exists_right _ _ _ hp)
    (fun h hq => hq) (cpsTripleWithin_exists_pre_gen (fun g5 => ?_))
  refine cpsTripleWithin_weaken hvbf_pure_pull_last (fun h hq => hq)
    (cpsTripleWithin_pure_pre (fun hrel => ?_))
  -- the BNE frame: everything but a0/x0
  have hbne := bne_spec_gen_within .x10 .x0 (40 : BitVec 13) status (0 : Word) (K + 40)
  rw [show (K + 40 : Word) + 4 = K + 44 from by decide,
    show (K + 40 : Word) + signExtend13 (40 : BitVec 13) = K + 80 from by decide] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (fun a i hi => hvbf_mono a i (hvbf_mem 10 (.BNE .x10 .x0 (40 : BitVec 13)) (K + 40)
      (by decide) (by rw [hvbf_length]; decide) rfl a i hi)) hbne
  have hbneF := cpsBranchWithin_frameR
    (hvbfBrFrame spC spH spM Ret hdrFeePtr parentFeePtr
          v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 hdrFeeBytes parentFeeBytes outBytes accBytes G)
    (by pcf) hbneC
  -- K73 failure arm (taken): status 2
  have hfailCont : cpsTripleWithin
      (11 + (u256EqBody hdrFeePtr hvbfScratchAddr hdrFeeBytes
        (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes))).steps)
      (K + 80) Ret hvbfWholeCode
      (((.x10 ↦ᵣ status) ** ((.x0 ↦ᵣ (0 : Word)) ** ⌜status ≠ (0 : Word)⌝)) **
        (hvbfBrFrame spC spH spM Ret hdrFeePtr parentFeePtr
          v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 hdrFeeBytes parentFeeBytes outBytes accBytes G))
      (hvbfRetPost sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
        v8 v9 v18 v19 v20 hdrFeeBytes parentFeeBytes accBytes G) := by
    refine cpsTripleWithin_weaken hvbf_pure_pull_branch (fun h hq => hq)
      (cpsTripleWithin_pure_pre (fun hne => ?_))
    have hli := li_spec_gen_within .x10 status (2 : Word) (K + 80) (by decide)
    rw [show (K + 80 : Word) + 4 = K + 84 from by decide] at hli
    have hliC := cpsTripleWithin_extend_code
      (fun a i hi => hvbf_mono a i (hvbf_mem 20 (.LI .x10 (2 : Word)) (K + 80)
        (by decide) (by rw [hvbf_length]; decide) rfl a i hi)) hli
    have hliF := cpsTripleWithin_frameR
      ((.x0 ↦ᵣ (0 : Word)) ** (hvbfBrFrame spC spH spM Ret hdrFeePtr parentFeePtr
          v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 hdrFeeBytes parentFeeBytes outBytes accBytes G)) (by pcf) hliC
    have hep := hvbfEpilogue sp0 spC Ret (K + 40) hdrFeePtr (2 : Word) v8
      ((.x0 ↦ᵣ (0 : Word)) ** (hvbfArmFrame spH spM hdrFeePtr parentFeePtr
            v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 hdrFeeBytes parentFeeBytes outBytes accBytes G))
      (by pcf) hspC hret
    have hseq := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by unfold hvbfBrFrame at hp; unfold hvbfArmFrame; xperm_hyp hp) hliF hep
    have hseqM := cpsTripleWithin_mono_nSteps
      (show 1 + 4 ≤ 11 + (u256EqBody hdrFeePtr hvbfScratchAddr hdrFeeBytes
        (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes))).steps
        from by omega) hseq
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hseqM
    unfold hvbfRetPost hvbfRetK73FailPost
    refine Or.inr (Or.inr ?_)
    refine ⟨g0, g1, g2, g3, g4, g5, outBytes, status, ?_⟩
    refine (sepConj_pure_right _).2 ⟨?_, hne, hrel.2⟩
    unfold hvbfRetK73FailState hvbfRetCommon
    unfold hvbfArmFrame at hq
    xperm_hyp hq
  -- K73 success arm (not taken): scratch holds the expected encoding
  have hsuccCont : cpsTripleWithin
      (11 + (u256EqBody hdrFeePtr hvbfScratchAddr hdrFeeBytes
        (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes))).steps)
      (K + 44) Ret hvbfWholeCode
      (((.x10 ↦ᵣ status) ** ((.x0 ↦ᵣ (0 : Word)) ** ⌜status = (0 : Word)⌝)) **
        (hvbfBrFrame spC spH spM Ret hdrFeePtr parentFeePtr
          v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5 hdrFeeBytes parentFeeBytes outBytes accBytes G))
      (hvbfRetPost sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
        v8 v9 v18 v19 v20 hdrFeeBytes parentFeeBytes accBytes G) := by
    refine cpsTripleWithin_weaken hvbf_pure_pull_branch (fun h hq => hq)
      (cpsTripleWithin_pure_pre (fun hst => ?_))
    subst hst
    have hbytes : outBytes =
        natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes) := hrel.1 rfl
    subst hbytes
    have hsucc := hvbfSuccessCont sp0 spC spH spM Ret hdrFeePtr parentFeePtr
      gasLimit gasUsed v8 v9 v18 v19 v20 g0 g1 g2 g3 g4 g5
      hdrFeeBytes parentFeeBytes accBytes G hG hspC hret hlenHdr hwfHdr hdisjHdrScr
    refine cpsTripleWithin_weaken (fun h hp => by unfold hvbfBrFrame at hp; xperm_hyp hp)
      (fun h hq => ?_) hsucc
    unfold hvbfEqPost at hq
    unfold hvbfRetPost
    rcases hq with hA | hB
    · exact Or.inl hA
    · exact Or.inr (Or.inl hB)
  have hmerge := cpsBranchWithin_merge_same_cr hbneF hfailCont hsuccCont
  refine cpsTripleWithin_mono_nSteps ?_ (cpsTripleWithin_weaken
    (fun h hp => by unfold hvbfBrFrame; xperm_hyp hp) (fun h hq => hq) hmerge)
  omega

/-! ## §12  The whole-routine triple -/

/-- The `header_validate_base_fee` wrapper, entry to caller return: within
    the static step bound, the machine returns to `Ret` in one of the three
    outcome states of `hvbfRetPost` — match (0), base-fee mismatch (1,
    attributed to the reference's `.invalidBlock "base fee mismatch"`), or
    K73 compute failure (2, guest-internal).  The K73 callee contract is the
    named remaining premise `hcallee` (the K73 family is `.partly`). -/
theorem header_validate_base_fee_spec_within
    (nK73 : Nat)
    (sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed : Word)
    (v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5 : Word)
    (hdrFeeBytes parentFeeBytes scratchBytes accBytes : List (BitVec 8))
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-16 : BitVec 12))
    (_hspH : spH = spC + signExtend12 (-56 : BitVec 12))
    (_hspM : spM = spH + signExtend12 (-48 : BitVec 12))
    (hret : Ret &&& ~~~(1 : Word) = Ret)
    (hlenHdr : hdrFeeBytes.length = 32)
    (hwfHdr : Region.wf ⟨hdrFeePtr, hdrFeeBytes⟩)
    (_hlenPar : parentFeeBytes.length = 32)
    (_hwfPar : Region.wf ⟨parentFeePtr, parentFeeBytes⟩)
    (_hlenScr : scratchBytes.length = 32)
    (_hlenAcc : accBytes.length = 40)
    (hdisjHdrScr : hdrFeePtr.toNat + 32 ≤ hvbfScratchAddr.toNat ∨
      hvbfScratchAddr.toNat + 32 ≤ hdrFeePtr.toNat)
    (_hdisjParScr : parentFeePtr.toNat + 32 ≤ hvbfScratchAddr.toNat ∨
      hvbfScratchAddr.toNat + 32 ≤ parentFeePtr.toNat)
    (hcallee : cpsTripleWithin nK73 K73 (K + 40) wholeCode
      (((.x1 : Reg) ↦ᵣ (K + 40)) **
        hvbfK73CalleePre spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
          v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5
          hdrFeeBytes parentFeeBytes scratchBytes accBytes G)
      (((.x1 : Reg) ↦ᵣ (K + 40)) ** hvbfK73CalleePost spC spH spM Ret hdrFeePtr parentFeePtr
          v8 v9 v18 v19 v20 hdrFeeBytes parentFeeBytes accBytes
          (hvbfExpected gasLimit gasUsed parentFeeBytes) G)) :
    cpsTripleWithin
      ((10 + nK73) + (12 + (u256EqBody hdrFeePtr hvbfScratchAddr hdrFeeBytes
        (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes))).steps))
      K Ret hvbfWholeCode
      (hvbfPre sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
        v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5
        hdrFeeBytes parentFeeBytes scratchBytes accBytes G)
      (hvbfRetPost sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
        v8 v9 v18 v19 v20 hdrFeeBytes parentFeeBytes accBytes G) := by
  have hpro := hvbfPrologue sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
    v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5
    hdrFeeBytes parentFeeBytes scratchBytes accBytes G hG hspC
  have hcall := hvbfK73Call nK73 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
    v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5
    hdrFeeBytes parentFeeBytes scratchBytes accBytes G hG hcallee
  have hfront := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hpro hcall
  have hback := hvbfDispatch sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
    v8 v9 v18 v19 v20 hdrFeeBytes parentFeeBytes accBytes G hG hspC hret
    hlenHdr hwfHdr hdisjHdrScr
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hfront hback
  exact cpsTripleWithin_mono_nSteps
    (show (9 + (1 + nK73)) + (12 + (u256EqBody hdrFeePtr hvbfScratchAddr hdrFeeBytes
        (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes))).steps) ≤
      (10 + nK73) + (12 + (u256EqBody hdrFeePtr hvbfScratchAddr hdrFeeBytes
        (natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes))).steps)
      from by omega) hall

/-! ## §13  Non-vacuity: a concrete inhabitant of the static premise set -/

/-- The whole-routine theorem's static premise set is inhabited: at the
    input-region base for the header fee, the adjacent 32 bytes for the
    parent fee, a literal stack pointer, zero-filled scratch/accumulator, and
    the empty ambient frame, every static premise holds and the entry
    assertion is pc-free, with the four byte windows and the 120-byte stack
    block pairwise disjoint (layout facts decided here — never premises on
    the triple).  The K73 callee contract `hcallee` remains a named
    hypothesis of the main theorem (the K73 family's remaining work), exactly
    like `hcore` in `validate_header_cps_compose`. -/
theorem header_validate_base_fee_spec_within_inhabitable :
    ∃ (sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed : Word)
      (v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5 : Word)
      (hdrFeeBytes parentFeeBytes scratchBytes accBytes : List (BitVec 8))
      (G : Assertion),
      G.pcFree ∧
      (spC = sp0 + signExtend12 (-16 : BitVec 12)) ∧
      (spH = spC + signExtend12 (-56 : BitVec 12)) ∧
      (spM = spH + signExtend12 (-48 : BitVec 12)) ∧
      (Ret &&& ~~~(1 : Word) = Ret) ∧
      hdrFeeBytes.length = 32 ∧
      Region.wf ⟨hdrFeePtr, hdrFeeBytes⟩ ∧
      parentFeeBytes.length = 32 ∧
      Region.wf ⟨parentFeePtr, parentFeeBytes⟩ ∧
      scratchBytes.length = 32 ∧
      accBytes.length = 40 ∧
      (hdrFeePtr.toNat + 32 ≤ hvbfScratchAddr.toNat ∨
        hvbfScratchAddr.toNat + 32 ≤ hdrFeePtr.toNat) ∧
      (parentFeePtr.toNat + 32 ≤ hvbfScratchAddr.toNat ∨
        hvbfScratchAddr.toNat + 32 ≤ parentFeePtr.toNat) ∧
      (hvbfPre sp0 spC spH spM Ret hdrFeePtr parentFeePtr gasLimit gasUsed
        v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5
        hdrFeeBytes parentFeeBytes scratchBytes accBytes G).pcFree ∧
      -- layout facts (decided at the witness valuation)
      ((0x40000000 : Nat) + 32 ≤ 0x40000020 ∨ (0x40000020 : Nat) + 32 ≤ 0x40000000) ∧
      ((0x40000040 : Nat) ≤ U256MulU64Be.accBase.toNat ∨
        U256MulU64Be.accBase.toNat + 40 ≤ 0x40000000) ∧
      (U256MulU64Be.accBase.toNat + 40 ≤ hvbfScratchAddr.toNat ∨
        hvbfScratchAddr.toNat + 32 ≤ U256MulU64Be.accBase.toNat) ∧
      ((0x10000 : Nat) ≤ 0x40000000 ∨ (0x40000040 : Nat) ≤ 0xff88) ∧
      ((0x10000 : Nat) ≤ U256MulU64Be.accBase.toNat ∨
        hvbfScratchAddr.toNat + 32 ≤ 0xff88) := by
  refine ⟨(0x10000 : Word), (0xfff0 : Word), (0xffb8 : Word), (0xff88 : Word),
    (0x100 : Word), (0x40000000 : Word), (0x40000020 : Word),
    (5000 : Word), (5000 : Word),
    (0 : Word), (0 : Word), (0 : Word), (0 : Word), (0 : Word),
    (0 : Word), (0 : Word), (0 : Word), (0 : Word), (0 : Word), (0 : Word),
    List.replicate 32 (0 : BitVec 8), List.replicate 32 (0 : BitVec 8),
    List.replicate 32 (0 : BitVec 8), List.replicate 40 (0 : BitVec 8),
    empAssertion, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact pcFree_emp
  all_goals (first
    | (unfold hvbfPre U256MulU64Be.frameSlots; pcf)
    | decide)

end EvmAsm.Codegen.HeaderValidateBaseFeeSpec
