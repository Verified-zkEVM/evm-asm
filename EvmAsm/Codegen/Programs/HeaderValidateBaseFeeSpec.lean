/-
  Caller contract for `header_validate_base_fee` (K74).

  The emitted wrapper is a 25-instruction ABI frame around K73's base-fee
  calculator and the bytewise `u256_eq` helper.  This file intentionally keeps
  both callee contracts explicit: K73 has no unconditional whole-routine
  machine triple yet, and the wrapper must not turn that missing proof into an
  implicit assumption.

  K74's flat contract deliberately owns x14--x17 as a contract artifact.  The
  linked K73, K74, `u256_div_u64_be`, `u256_sub_be`, and `u256_add_be` streams
  do not touch those registers; the ownership is present only so the item-10
  K73 triple composes at this caller boundary.  This is not a machine-clobber
  claim, and the general frame-cancellation infrastructure is deferred to
  issue 12770.  An upstream `validate_header` caller must supply these four
  ownership atoms in its residual frame.
-/

import EvmAsm.Codegen.Programs.HeaderBaseFee
import EvmAsm.Codegen.Programs.HeaderBaseFeeSpec
import EvmAsm.Codegen.Programs.U256EqSAsm
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Codegen.HeaderValidateBaseFeeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec

abbrev H : Word := (GuestAddrs.header_validate_base_fee : Word)
abbrev K73 : Word := (GuestAddrs.eip1559_calc_base_fee_per_gas : Word)
abbrev EqK : Word := (GuestAddrs.u256_eq : Word)
abbrev hvbfProg : Program := EvmAsm.Codegen.headerValidateBaseFee_prog
abbrev hvbfCode : CodeReq := CodeReq.ofProg H hvbfProg

abbrev Expected : Word := (GuestAddrs.hvbf_expected : Word)

/-! Flat-contract ownership required by the item-10 K73 composition.  Keep
    this wrapper local to K74: issue 12770 owns any shared frame-cancellation
    infrastructure, and these atoms are not evidence that the machine writes
    x14--x17. -/
def k74FlatFrame (F : Assertion) : Assertion :=
  regOwns [.x14, .x15, .x16, .x17] ** F

def hvbfFrame : FrameDesc := [(.x1, 0), (.x8, 8)]

def hvbfSaved (raIn old8 : Word) : Reg → Word := fun r => match r with
  | .x1 => raIn
  | .x8 => old8
  | _ => 0

theorem hvbf_length : hvbfProg.length = 25 := by decide

theorem hvbf_mono {cr : CodeReq}
    (hcode : ∀ a i, hvbfCode a = some i → cr a = some i) :
    ∀ a i, hvbfCode a = some i → cr a = some i := hcode

/-! The state after K73 returns to the wrapper.  `tailRest` deliberately omits
    x1, x2, x8, x10 and x11: those are the link/stack/header/status registers
    changed by the wrapper's final dispatch and epilogue.  K73's mul callee
    also clobbers x13 and does not restore it, so the post owns x13 rather than
    falsely claiming that the wrapper's `Expected` pointer survived. -/

def tailRestCore
    (_spH spK _raIn _old8 headerPtr v9 target v19 v20 _gasUsed parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (F : Assertion) :
    Assertion :=
  (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ target) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
  (.x12 ↦ᵣ parentPtr) ** regOwn .x13 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 **
  frameSlotsSaved k73Frame spK
    (k73Saved (H + 40) headerPtr v9 target v19 v20) **
  bytesRegion headerPtr headerBytes ** bytesRegion parentPtr parentBytes **
  bytesRegion Expected expectedBytes ** F

def tailRest
    (spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (F : Assertion) :
    Assertion :=
  frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
  tailRestCore spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

/-! The K73 failure path is allowed to overwrite the caller-owned expected
    buffer before returning a nonzero status.  Keep that written image in the
    post rather than weakening it to `regOwn`: the next consumer may need the
    bytes, and the whole-routine K73 triple must describe the actual write. -/
def tailRestScratch
    (spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr : Word)
    (parentBytes scratchBytes headerBytes : List (BitVec 8)) (F : Assertion) :
    Assertion :=
  frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
  tailRestCore spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
    parentBytes scratchBytes headerBytes F

def k73PreRest
    (spH spK headerPtr v9 v18 v19 v20 gasLimit gasUsed parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (raIn old8 : Word) (F : Assertion) : Assertion :=
  (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
  (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
  (.x10 ↦ᵣ gasLimit) ** (.x11 ↦ᵣ gasUsed) **
  (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ Expected) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
  frameSlotsOwn k73Frame spK **
  frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
  bytesRegion headerPtr headerBytes ** bytesRegion parentPtr parentBytes **
  bytesRegion Expected expectedBytes ** F

def k73PostRest
    (spH spK headerPtr v9 target v19 v20 gasUsed parentPtr status : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (raIn old8 : Word) (F : Assertion) : Assertion :=
  (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) ** (.x10 ↦ᵣ status) **
  (.x11 ↦ᵣ gasUsed) ** (.x0 ↦ᵣ (0 : Word)) **
  tailRest spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

def k73PostOwn
    (spH spK headerPtr v9 target v19 v20 gasUsed parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (raIn old8 : Word) (F : Assertion) : Assertion :=
  (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) ** regOwn .x10 **
  (.x11 ↦ᵣ gasUsed) ** (.x0 ↦ᵣ (0 : Word)) **
  tailRest spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

def k73FailurePost
    (spH spK headerPtr v9 target v19 v20 gasUsed parentPtr status : Word)
    (parentBytes scratchBytes headerBytes : List (BitVec 8))
    (raIn old8 : Word) (F : Assertion) : Assertion :=
  (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) ** (.x10 ↦ᵣ status) **
  (.x11 ↦ᵣ gasUsed) ** (.x0 ↦ᵣ (0 : Word)) **
  tailRestScratch spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
    parentBytes scratchBytes headerBytes F

/-! The normalized K73 post consumed by K74.  The successful arm is the
    established fixed-byte post; the failure arm retains both the nonzero
    status and the bytes actually left in the shared output window. -/
def k73CallPost
    (spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (F : Assertion) :
    Assertion := fun h =>
  k73PostOwn spH spK headerPtr v9 target v19 v20 gasUsed parentPtr
      parentBytes expectedBytes headerBytes raIn old8 F h ∨
  ∃ status scratchBytes,
    status ≠ (0 : Word) ∧
    k73FailurePost spH spK headerPtr v9 target v19 v20 gasUsed parentPtr status
      parentBytes scratchBytes headerBytes raIn old8 F h

def hvbfPre
    (sp0 spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr : Word)
    (v9 v18 v19 v20 : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ old8) ** (.x9 ↦ᵣ v9) **
  (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
  (.x10 ↦ᵣ headerPtr) ** (.x11 ↦ᵣ gasLimit) **
  (.x12 ↦ᵣ gasUsed) ** (.x13 ↦ᵣ parentPtr) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
  frameSlotsOwn hvbfFrame spH ** frameSlotsOwn k73Frame spK **
  bytesRegion headerPtr headerBytes ** bytesRegion parentPtr parentBytes **
  bytesRegion Expected expectedBytes ** F

def eqPre
    (spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  (.x10 ↦ᵣ headerPtr) ** (.x11 ↦ᵣ Expected) ** (.x0 ↦ᵣ (0 : Word)) **
  tailRest spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

def eqPost
    (spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr eqStatus : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  (.x10 ↦ᵣ eqStatus) ** (.x11 ↦ᵣ Expected) ** (.x0 ↦ᵣ (0 : Word)) **
  tailRest spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

def eqPostAny
    (spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (F : Assertion) : Assertion := fun h =>
  ∃ eqStatus,
    eqPost spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr eqStatus
      parentBytes expectedBytes headerBytes F h

def eqPostOwn
    (spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  regOwn .x10 ** (.x11 ↦ᵣ Expected) ** (.x0 ↦ᵣ (0 : Word)) **
  tailRest spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

def k73PostAny
    (spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (F : Assertion) : Assertion := fun h =>
  ∃ status,
    k73PostRest spH spK headerPtr v9 target v19 v20 gasUsed parentPtr status
      parentBytes expectedBytes headerBytes raIn old8 F h

def hvbfFinal
    (sp0 spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
      status out11 : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ old8) **
  (.x10 ↦ᵣ status) ** (.x11 ↦ᵣ out11) ** (.x0 ↦ᵣ (0 : Word)) **
  tailRest spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

def hvbfFinalScratch
    (sp0 spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
      status out11 : Word)
    (parentBytes scratchBytes headerBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ old8) **
  (.x10 ↦ᵣ status) ** (.x11 ↦ᵣ out11) ** (.x0 ↦ᵣ (0 : Word)) **
  tailRestScratch spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
    parentBytes scratchBytes headerBytes F

def hvbfFinalAny
    (sp0 spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (F : Assertion) : Assertion := fun h =>
  (∃ scratchBytes,
    hvbfFinalScratch sp0 spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed
      parentPtr (2 : Word) gasUsed parentBytes scratchBytes headerBytes F h) ∨
    hvbfFinal sp0 spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
      (0 : Word) Expected parentBytes expectedBytes headerBytes F h ∨
    hvbfFinal sp0 spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
      (1 : Word) Expected parentBytes expectedBytes headerBytes F h

def hvbfFinalOwn
    (sp0 spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ old8) ** regOwn .x10 **
  (.x11 ↦ᵣ gasUsed) ** (.x0 ↦ᵣ (0 : Word)) **
  tailRest spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

def hvbfDispatchPost
    (spH spK raIn old8 headerPtr gasUsed parentPtr : Word)
    (v9 target v19 v20 : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (F : Assertion) :
    Assertion :=
  (.x1 ↦ᵣ (H + 40)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
  regOwn .x10 ** (.x11 ↦ᵣ gasUsed) ** (.x0 ↦ᵣ (0 : Word)) **
  tailRest spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

def hvbfEqDispatchPost
    (spH spK raIn old8 headerPtr gasUsed parentPtr : Word)
    (v9 target v19 v20 : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (F : Assertion) :
    Assertion :=
  (.x1 ↦ᵣ (H + 60)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
  regOwn .x10 ** (.x11 ↦ᵣ Expected) ** (.x0 ↦ᵣ (0 : Word)) **
  tailRest spH spK raIn old8 headerPtr
    v9 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

def hvbfEpiPre
    (spH spK raIn old8 headerPtr raBefore status gasUsed parentPtr : Word)
    (v9 target v19 v20 : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (F : Assertion) :
    Assertion :=
  (.x1 ↦ᵣ raBefore) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
  (.x10 ↦ᵣ status) ** (.x11 ↦ᵣ gasUsed) ** (.x0 ↦ᵣ (0 : Word)) **
  frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
  tailRestCore spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

def hvbfEqPrefixPost
    (spH spK raIn old8 headerPtr gasUsed parentPtr : Word)
    (v9 target v19 v20 : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (F : Assertion) :
    Assertion :=
  (.x1 ↦ᵣ (H + 40)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
  (.x10 ↦ᵣ headerPtr) ** (.x11 ↦ᵣ gasUsed) ** (.x0 ↦ᵣ (0 : Word)) **
  tailRest spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

/-! ## Prefix and K73 call

The first theorem is intentionally standalone: it is the wrapper's actual
machine prefix, not a restatement of the existing caller adapter. -/

theorem hvbfHead
    (sp0 spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr : Word)
    (v9 v18 v19 v20 : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (F : Assertion)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (_hspK : spK = spH + signExtend12 (-56 : BitVec 12))
    (hF : F.pcFree)
    {cr : CodeReq}
    (hcode : ∀ a i, hvbfCode a = some i → cr a = some i) :
    cpsTripleWithin 9 H (H + 36) cr
      (hvbfPre sp0 spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      ((.x1 ↦ᵣ raIn) **
        (k73PreRest spH spK headerPtr v9 v18 v19 v20 gasLimit gasUsed parentPtr
          parentBytes expectedBytes headerBytes raIn old8 F)) := by
  have h0 := addi_spec_gen_same_within .x2 sp0 (-16 : BitVec 12) H (by decide)
  rw [← hspH] at h0
  have h0' := cpsTripleWithin_extend_code hcode
    (cpsTripleWithin_extend_code (cr' := hvbfCode)
      (CodeReq.ofProg_mem_at H H hvbfProg 0
        (.ADDI .x2 .x2 (-16 : BitVec 12)) (by decide)
        (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide)) h0)
  have h1 := sd_spec_gen_own_within .x2 .x1 spH raIn (0 : BitVec 12) (H + 4)
  have h1' := cpsTripleWithin_extend_code hcode
    (cpsTripleWithin_extend_code (cr' := hvbfCode)
      (CodeReq.ofProg_mem_at H (H + 4) hvbfProg 1
        (.SD .x2 .x1 (0 : BitVec 12)) (by bv_omega)
        (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide)) h1)
  have h2 := sd_spec_gen_own_within .x2 .x8 spH old8 (8 : BitVec 12) (H + 8)
  have h2' := cpsTripleWithin_extend_code hcode
    (cpsTripleWithin_extend_code (cr' := hvbfCode)
      (CodeReq.ofProg_mem_at H (H + 8) hvbfProg 2
        (.SD .x2 .x8 (8 : BitVec 12)) (by bv_omega)
        (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide)) h2)
  have h3 := mv_spec_gen_within .x8 .x10 headerPtr old8 (H + 12) (by decide)
  have h3' := cpsTripleWithin_extend_code hcode
    (cpsTripleWithin_extend_code (cr' := hvbfCode)
      (CodeReq.ofProg_mem_at H (H + 12) hvbfProg 3
        (.MV .x8 .x10) (by bv_omega) (by rw [hvbf_length]; decide) rfl
        (by rw [hvbf_length]; decide)) h3)
  have h4 := mv_spec_gen_within .x10 .x11 gasLimit headerPtr (H + 16) (by decide)
  have h4' := cpsTripleWithin_extend_code hcode
    (cpsTripleWithin_extend_code (cr' := hvbfCode)
      (CodeReq.ofProg_mem_at H (H + 16) hvbfProg 4
        (.MV .x10 .x11) (by bv_omega) (by rw [hvbf_length]; decide) rfl
        (by rw [hvbf_length]; decide)) h4)
  have h5 := mv_spec_gen_within .x11 .x12 gasUsed gasLimit (H + 20) (by decide)
  have h5' := cpsTripleWithin_extend_code hcode
    (cpsTripleWithin_extend_code (cr' := hvbfCode)
      (CodeReq.ofProg_mem_at H (H + 20) hvbfProg 5
        (.MV .x11 .x12) (by bv_omega) (by rw [hvbf_length]; decide) rfl
        (by rw [hvbf_length]; decide)) h5)
  have h6 := mv_spec_gen_within .x12 .x13 parentPtr gasUsed (H + 24) (by decide)
  have h6' := cpsTripleWithin_extend_code hcode
    (cpsTripleWithin_extend_code (cr' := hvbfCode)
      (CodeReq.ofProg_mem_at H (H + 24) hvbfProg 6
        (.MV .x12 .x13) (by bv_omega) (by rw [hvbf_length]; decide) rfl
        (by rw [hvbf_length]; decide)) h6)
  have hau := CodeReq.ofProg_mem_at H (H + 28) hvbfProg 7
    (.AUIPC .x13 (laHi GuestAddrs.hvbf_expected (GuestAddrs.header_validate_base_fee + 28)))
    (by bv_omega) (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide)
  have had := CodeReq.ofProg_mem_at H (H + 32) hvbfProg 8
    (.ADDI .x13 .x13 (laLo GuestAddrs.hvbf_expected
      (GuestAddrs.header_validate_base_fee + 28)))
    (by bv_omega) (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide)
  have h8 := EvmAsm.Rv64.la_materialize_within .x13 parentPtr (H + 28) Expected
    (by decide) (by unfold H Expected; decide)
    (fun a i hi => hcode a i (hau a i hi))
    (fun a i hi => hcode a i (had a i hi))
  have h0F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ old8) ** (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
      (.x10 ↦ᵣ headerPtr) ** (.x11 ↦ᵣ gasLimit) ** (.x12 ↦ᵣ gasUsed) **
      (.x13 ↦ᵣ parentPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsOwn hvbfFrame spH **
      frameSlotsOwn k73Frame spK ** bytesRegion headerPtr headerBytes **
      bytesRegion parentPtr parentBytes ** bytesRegion Expected expectedBytes ** F)
    (by pcf; exact hF) h0'
  have h1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ old8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
      (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ headerPtr) **
      (.x11 ↦ᵣ gasLimit) ** (.x12 ↦ᵣ gasUsed) ** (.x13 ↦ᵣ parentPtr) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      memOwn (spH + signExtend12 (8 : BitVec 12)) ** frameSlotsOwn k73Frame spK **
      bytesRegion headerPtr headerBytes ** bytesRegion parentPtr parentBytes **
    bytesRegion Expected expectedBytes ** F) (by pcf; exact hF) h1'
  have h2F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
      (.x10 ↦ᵣ headerPtr) ** (.x11 ↦ᵣ gasLimit) ** (.x12 ↦ᵣ gasUsed) **
      (.x13 ↦ᵣ parentPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** ((spH + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) **
      frameSlotsOwn k73Frame spK **
      bytesRegion headerPtr headerBytes ** bytesRegion parentPtr parentBytes **
      bytesRegion Expected expectedBytes ** F) (by pcf; exact hF) h2'
  have h3F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spH) ** (.x1 ↦ᵣ raIn) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
      (.x20 ↦ᵣ v20) ** (.x11 ↦ᵣ gasLimit) ** (.x12 ↦ᵣ gasUsed) **
      (.x13 ↦ᵣ parentPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
      frameSlotsOwn k73Frame spK **
      bytesRegion headerPtr headerBytes ** bytesRegion parentPtr parentBytes **
      bytesRegion Expected expectedBytes ** F) (by pcf; exact hF) h3'
  have h4F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spH) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
      (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
      (.x12 ↦ᵣ gasUsed) ** (.x13 ↦ᵣ parentPtr) ** regOwn .x5 ** regOwn .x6 **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
      frameSlotsOwn k73Frame spK **
      bytesRegion headerPtr headerBytes ** bytesRegion parentPtr parentBytes **
      bytesRegion Expected expectedBytes ** F) (by pcf; exact hF) h4'
  have h5F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spH) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
      (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ gasLimit) **
      (.x13 ↦ᵣ parentPtr) ** regOwn .x5 ** regOwn .x6 **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
      frameSlotsOwn k73Frame spK **
      bytesRegion headerPtr headerBytes ** bytesRegion parentPtr parentBytes **
      bytesRegion Expected expectedBytes ** F) (by pcf; exact hF) h5'
  have h6F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spH) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
      (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ gasLimit) **
      (.x11 ↦ᵣ gasUsed) ** regOwn .x5 ** regOwn .x6 **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
      frameSlotsOwn k73Frame spK **
      bytesRegion headerPtr headerBytes ** bytesRegion parentPtr parentBytes **
      bytesRegion Expected expectedBytes ** F) (by pcf; exact hF) h6'
  have h8F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spH) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
      (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ gasLimit) **
      (.x11 ↦ᵣ gasUsed) ** (.x12 ↦ᵣ parentPtr) ** regOwn .x5 ** regOwn .x6 **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
      frameSlotsOwn k73Frame spK **
      bytesRegion headerPtr headerBytes ** bytesRegion parentPtr parentBytes **
      bytesRegion Expected expectedBytes ** F) (by pcf; exact hF) h8
  have hOwn :
      frameSlotsOwn hvbfFrame spH =
        (memOwn (spH + signExtend12 (0 : BitVec 12)) **
          memOwn (spH + signExtend12 (8 : BitVec 12))) := by
    change (memOwn (spH + signExtend12 (0 : BitVec 12)) **
      (memOwn (spH + signExtend12 (8 : BitVec 12)) ** empAssertion)) = _
    rw [sepConj_emp_right']
  have hSaved :
      frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) =
        (((spH + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) **
          ((spH + signExtend12 (8 : BitVec 12)) ↦ₘ old8)) := by
    change (((spH + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) **
      (((spH + signExtend12 (8 : BitVec 12)) ↦ₘ old8) ** empAssertion)) = _
    rw [sepConj_emp_right']
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [hOwn] at hp
    xperm_hyp hp) h0F h1F
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    xperm_hyp hp) h01 h2F
  have h0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [hSaved]
    xperm_hyp hp) h012 h3F
  have h0124 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    xperm_hyp hp) h0123 h4F
  have h0125 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    xperm_hyp hp) h0124 h5F
  have h0126 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    xperm_hyp hp) h0125 h6F
  have h0128 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    xperm_hyp hp) h0126 h8F
  refine cpsTripleWithin_weaken (fun _ hp => by
      unfold hvbfPre at hp
      xperm_hyp hp)
    (fun _ hq => by
      simp only [k73PreRest]
      xperm_hyp hq) h0128

theorem header_validate_base_fee_k73_call_spec_within
    {cr calleeCode : CodeReq} {n : Nat}
    (sp0 spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr : Word)
    (v9 v18 v19 v20 : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (F : Assertion)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hspK : spK = spH + signExtend12 (-56 : BitVec 12))
    (hF : F.pcFree)
    (hcode : ∀ a i, hvbfCode a = some i → cr a = some i)
    (hcalleeMono : ∀ a i, calleeCode a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n K73 (H + 40) calleeCode
      ((.x1 ↦ᵣ (H + 40)) **
        (k73PreRest spH spK headerPtr v9 v18 v19 v20 gasLimit gasUsed parentPtr
          parentBytes expectedBytes headerBytes raIn old8 F))
      ((.x1 ↦ᵣ (H + 40)) **
        k73CallPost spH spK raIn old8 headerPtr v9 (gasLimit >>> 1) v19 v20
          gasUsed parentPtr parentBytes expectedBytes headerBytes F)) :
    cpsTripleWithin (10 + n) H (H + 40) cr
      (hvbfPre sp0 spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      ((.x1 ↦ᵣ (H + 40)) **
        k73CallPost spH spK raIn old8 headerPtr v9 (gasLimit >>> 1) v19 v20
          gasUsed parentPtr parentBytes expectedBytes headerBytes F) := by
  have hhead := hvbfHead sp0 spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr
    v9 v18 v19 v20 parentBytes expectedBytes headerBytes F hspH hspK hF hcode
  have hmem : ∀ a i,
      CodeReq.singleton (H + 36)
        (.JAL .x1 (jalOff GuestAddrs.eip1559_calc_base_fee_per_gas
          (GuestAddrs.header_validate_base_fee + 36))) a = some i → cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 36) hvbfProg 9
      (.JAL .x1 (jalOff GuestAddrs.eip1559_calc_base_fee_per_gas
        (GuestAddrs.header_validate_base_fee + 36))) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have hcalleeCr := cpsTripleWithin_extend_code hcalleeMono hcallee
  have hcall := callWithin_spec (cr := cr)
    (P := k73PreRest spH spK headerPtr v9 v18 v19 v20 gasLimit gasUsed parentPtr
      parentBytes expectedBytes headerBytes raIn old8 F)
    (Q := k73CallPost spH spK raIn old8 headerPtr v9 (gasLimit >>> 1) v19 v20
      gasUsed parentPtr parentBytes expectedBytes headerBytes F)
    (H + 36) K73 raIn
      (jalOff GuestAddrs.eip1559_calc_base_fee_per_gas
        (GuestAddrs.header_validate_base_fee + 36)) n
    (by exact jalOff_correct_add GuestAddrs.eip1559_calc_base_fee_per_gas
          GuestAddrs.header_validate_base_fee 36 (by decide) (by decide)
          (by decide) (by decide)) hmem
    (by pcf; exact hF) hcalleeCr
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hhead hcall
  have hentry : H + 36 + 4 = H + 40 := by bv_omega
  rw [hentry] at hseq
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hseq

/-! The shared epilogue is kept separate so the two status paths can use it
    with their different link values (`H+40` and `H+60`). -/

theorem hvbfEpilogue
    {cr : CodeReq}
    (sp0 spH raIn old8 headerPtr raBefore status out11 gasUsed : Word)
    (spK v9 target v19 v20 parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (F : Assertion)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hcode : ∀ a i, hvbfCode a = some i → cr a = some i)
    (hF : F.pcFree) :
    cpsTripleWithin 4 (H + 84) raIn cr
      ((.x1 ↦ᵣ raBefore) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
        (.x10 ↦ᵣ status) ** (.x11 ↦ᵣ out11) ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
        tailRestCore spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
          parentBytes expectedBytes headerBytes F)
      (hvbfFinal sp0 spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
        status out11 parentBytes expectedBytes headerBytes F) := by
  have h1 := ld_spec_gen_within .x1 .x2 spH raBefore raIn
    (0 : BitVec 12) (H + 84) (by decide)
  have h1' := cpsTripleWithin_extend_code hcode
    (cpsTripleWithin_extend_code (cr' := hvbfCode)
      (CodeReq.ofProg_mem_at H (H + 84) hvbfProg 21
        (.LD .x1 .x2 (0 : BitVec 12)) (by bv_omega)
        (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide)) h1)
  have h2 := ld_spec_gen_within .x8 .x2 spH headerPtr old8
    (8 : BitVec 12) (H + 88) (by decide)
  have h2' := cpsTripleWithin_extend_code hcode
    (cpsTripleWithin_extend_code (cr' := hvbfCode)
      (CodeReq.ofProg_mem_at H (H + 88) hvbfProg 22
        (.LD .x8 .x2 (8 : BitVec 12)) (by bv_omega)
        (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide)) h2)
  have h3 := addi_spec_gen_same_within .x2 spH (16 : BitVec 12) (H + 92) (by decide)
  rw [show spH + signExtend12 (16 : BitVec 12) = sp0 from by
    rw [hspH]
    exact sext_frameRestore sp0 (-16 : BitVec 12) (16 : BitVec 12) (by decide)] at h3
  have h3' := cpsTripleWithin_extend_code hcode
    (cpsTripleWithin_extend_code (cr' := hvbfCode)
      (CodeReq.ofProg_mem_at H (H + 92) hvbfProg 23
        (.ADDI .x2 .x2 (16 : BitVec 12)) (by bv_omega)
        (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide)) h3)
  have h4 := EvmAsm.Evm64.ret_spec_within' (H + 96) raIn
  rw [hret] at h4
  have h4' := cpsTripleWithin_extend_code hcode
    (cpsTripleWithin_extend_code (cr' := hvbfCode)
      (CodeReq.ofProg_mem_at H (H + 96) hvbfProg 24
        (.JALR .x0 .x1 (0 : BitVec 12)) (by bv_omega)
        (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide)) h4)
  have hSaved :
      frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) =
        (((spH + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) **
          ((spH + signExtend12 (8 : BitVec 12)) ↦ₘ old8)) := by
    change (((spH + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) **
      (((spH + signExtend12 (8 : BitVec 12)) ↦ₘ old8) ** empAssertion)) = _
    rw [sepConj_emp_right']
  have h1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ headerPtr) ** (.x10 ↦ᵣ status) ** (.x11 ↦ᵣ out11) **
      (.x0 ↦ᵣ (0 : Word)) **
      ((spH + signExtend12 (8 : BitVec 12)) ↦ₘ old8) **
      tailRestCore spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) (by pcf; exact hF) h1'
  have h2F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ status) ** (.x11 ↦ᵣ out11) **
      (.x0 ↦ᵣ (0 : Word)) **
      ((spH + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) **
      tailRestCore spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) (by pcf; exact hF) h2'
  have h3F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ old8) ** (.x10 ↦ᵣ status) **
      (.x11 ↦ᵣ out11) ** (.x0 ↦ᵣ (0 : Word)) **
      ((spH + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) **
      ((spH + signExtend12 (8 : BitVec 12)) ↦ₘ old8) **
      tailRestCore spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) (by pcf; exact hF) h3'
  have h4F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ old8) ** (.x10 ↦ᵣ status) **
      (.x11 ↦ᵣ out11) ** (.x0 ↦ᵣ (0 : Word)) **
      ((spH + signExtend12 (0 : BitVec 12)) ↦ₘ raIn) **
      ((spH + signExtend12 (8 : BitVec 12)) ↦ₘ old8) **
      tailRestCore spH spK raIn old8 headerPtr v9 target v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) (by pcf; exact hF) h4'
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h1F h2F
  have h123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h12 h3F
  have h1234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h123 h4F
  refine cpsTripleWithin_weaken (fun _ hp => by
      rw [hSaved] at hp
      xperm_hyp hp)
    (fun _ hq => by
      unfold hvbfFinal tailRest
      rw [hSaved]
      xperm_hyp hq) h1234

/-! A same-`CodeReq` branch may have different continuations on its two exits.
    The library's union-based rules are deliberately more general, but the
    wrapper's dispatch reuses one linked image for both paths. -/

theorem cpsBranchWithin_seq_two_triples_same_cr
    {nBranch nTaken nFall : Nat} {entry target fall exit_ : Word}
    {cr : CodeReq} {P Qt Qf Q : Assertion}
    (hBranch : cpsBranchWithin nBranch entry cr P target Qt fall Qf)
    (hTaken : cpsTripleWithin nTaken target exit_ cr Qt Q)
    (hFall : cpsTripleWithin nFall fall exit_ cr Qf Q) :
    cpsBranchWithin (nBranch + nTaken + nFall) entry cr P exit_ Q exit_ Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, hcase⟩ := hBranch R hR s hcr hPR hpc
  rcases hcase with ⟨hpc_t, hQtR⟩ | ⟨hpc_f, hQfR⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
    obtain ⟨k2, hk2, s2, hstep2, hpc2, hQR⟩ :=
      hTaken R hR s1 hcr' hQtR hpc_t
    exact ⟨k1 + k2, by omega, s2, stepN_add_eq hstep1 hstep2,
      Or.inl ⟨hpc2, hQR⟩⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
    obtain ⟨k2, hk2, s2, hstep2, hpc2, hQR⟩ :=
      hFall R hR s1 hcr' hQfR hpc_f
    exact ⟨k1 + k2, by omega, s2, stepN_add_eq hstep1 hstep2,
      Or.inr ⟨hpc2, hQR⟩⟩

theorem cpsBranchWithin_merge_two_bounds_same_cr
    {nBranch nTaken nFall : Nat} {entry target fall exit_ : Word}
    {cr : CodeReq} {P Qt Qf Q : Assertion}
    (hBranch : cpsBranchWithin nBranch entry cr P target Qt fall Qf)
    (hTaken : cpsTripleWithin nTaken target exit_ cr Qt Q)
    (hFall : cpsTripleWithin nFall fall exit_ cr Qf Q) :
    cpsTripleWithin (nBranch + nTaken + nFall) entry exit_ cr P Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, hcase⟩ := hBranch R hR s hcr hPR hpc
  rcases hcase with ⟨hpc_t, hQtR⟩ | ⟨hpc_f, hQfR⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
    obtain ⟨k2, hk2, s2, hstep2, hpc2, hQR⟩ :=
      hTaken R hR s1 hcr' hQtR hpc_t
    exact ⟨k1 + k2, by omega, s2, stepN_add_eq hstep1 hstep2, hpc2, hQR⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
    obtain ⟨k2, hk2, s2, hstep2, hpc2, hQR⟩ :=
      hFall R hR s1 hcr' hQfR hpc_f
    exact ⟨k1 + k2, by omega, s2, stepN_add_eq hstep1 hstep2, hpc2, hQR⟩

/-! ## Complete K74 wrapper

The two callee triples remain explicit premises.  The K73 premise is the
wrapper's only production seam; the equality helper is treated the same way
until its linked routine receives a corresponding whole-routine proof. -/

theorem header_validate_base_fee_spec_within
    {cr k73Code eqCode : CodeReq} {n73 nEq : Nat}
    (sp0 spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr : Word)
    (v9 old18 v19 v20 : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (G : Assertion)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hspK : spK = spH + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hG : G.pcFree)
    (hcode : ∀ a i, hvbfCode a = some i → cr a = some i)
    (hk73Mono : ∀ a i, k73Code a = some i → cr a = some i)
    (hk73 : cpsTripleWithin n73 K73 (H + 40) k73Code
      ((.x1 ↦ᵣ (H + 40)) **
        k73PreRest spH spK headerPtr v9 old18 v19 v20 gasLimit gasUsed parentPtr
          parentBytes expectedBytes headerBytes raIn old8 (k74FlatFrame G))
      ((.x1 ↦ᵣ (H + 40)) **
        k73CallPost spH spK raIn old8 headerPtr v9 (gasLimit >>> 1) v19 v20
          gasUsed parentPtr parentBytes expectedBytes headerBytes (k74FlatFrame G)))
    (heqMono : ∀ a i, eqCode a = some i → cr a = some i)
    (heq : cpsTripleWithin nEq EqK (H + 60) eqCode
      ((.x1 ↦ᵣ (H + 60)) **
        eqPre spH spK raIn old8 headerPtr v9 (gasLimit >>> 1) v19 v20 gasUsed parentPtr
          parentBytes expectedBytes headerBytes (k74FlatFrame G))
      ((.x1 ↦ᵣ (H + 60)) **
        eqPostOwn spH spK raIn old8 headerPtr v9 (gasLimit >>> 1) v19 v20 gasUsed parentPtr
          parentBytes expectedBytes headerBytes (k74FlatFrame G))) :
    cpsTripleWithin (27 + n73 + nEq) H raIn cr
      (hvbfPre sp0 spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr
        v9 old18 v19 v20 parentBytes expectedBytes headerBytes (k74FlatFrame G))
      (hvbfFinalAny sp0 spH spK raIn old8 headerPtr v9 (gasLimit >>> 1) v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes (k74FlatFrame G)) := by
  let F : Assertion := k74FlatFrame G
  have hF : G.pcFree := hG
  let v18 : Word := gasLimit >>> 1
  have hk73' := header_validate_base_fee_k73_call_spec_within
    (cr := cr) (calleeCode := k73Code) (n := n73)
    sp0 spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr
    v9 old18 v19 v20 parentBytes expectedBytes headerBytes F hspH hspK
    (by dsimp [F, k74FlatFrame]; pcf; exact hF) hcode
    hk73Mono hk73
  have hcall : cpsTripleWithin (10 + n73) H (H + 40) cr
      (hvbfPre sp0 spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr
        v9 old18 v19 v20 parentBytes expectedBytes headerBytes F)
      ((.x1 ↦ᵣ (H + 40)) **
        k73CallPost spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
          parentBytes expectedBytes headerBytes F) := by
    simpa only [F] using hk73'

  have hmem10 : ∀ a i,
      CodeReq.singleton (H + 40) (.BNE .x10 .x0 (40 : BitVec 13)) a = some i →
        cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 40) hvbfProg 10
      (.BNE .x10 .x0 (40 : BitVec 13)) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have hbne_values : ∀ status : Word, cpsBranchWithin 1 (H + 40) cr
      ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ status)) (H + 80)
        ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) (H + 44)
        ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) := by
    intro status
    have hb := bne_spec_gen_within .x10 .x0 (40 : BitVec 13) status
      (0 : Word) (H + 40)
    have hb' := cpsBranchWithin_extend_code hmem10 hb
    exact cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun h hq => by
        have hq' := sepConj_strip_pure_end2 h hq
        have hq'' : ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ status)) h := by
          xperm_hyp hq'
        exact sepConj_mono_right
          (regIs_implies_regOwn (r := .x10) (v := status)) h hq'')
      (fun h hq => by
        have hq' := sepConj_strip_pure_end2 h hq
        have hq'' : ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ status)) h := by
          xperm_hyp hq'
        exact sepConj_mono_right
          (regIs_implies_regOwn (r := .x10) (v := status)) h hq'') hb'
  have hbneOwn : cpsBranchWithin 1 (H + 40) cr
      ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) (H + 80)
        ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) (H + 44)
        ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) :=
    cpsBranchWithin_of_forall_regIs_to_regOwn
      (nSteps := 1) (entry := H + 40) (r := .x10)
      (P := (.x0 ↦ᵣ (0 : Word)))
      (exit_t := H + 80) (exit_f := H + 44)
      (Q_t := (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10)
      (Q_f := (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) hbne_values
  have hbneFrame := cpsBranchWithin_frameR
    ((.x1 ↦ᵣ (H + 40)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
      (.x11 ↦ᵣ gasUsed) ** tailRest spH spK raIn old8 headerPtr
        v9 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) (by pcf; exact hF) hbneOwn
  have hbne : cpsBranchWithin 1 (H + 40) cr
      (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (H + 80)
        (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
          v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (H + 44)
        (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
          v9 v18 v19 v20 parentBytes expectedBytes headerBytes F) := by
    refine cpsBranchWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_)
      (fun _ hq => ?_) hbneFrame
    · unfold hvbfDispatchPost at hp
      xperm_hyp hp
    · unfold hvbfDispatchPost
      xperm_hyp hq
    · unfold hvbfDispatchPost
      xperm_hyp hq

  have hmem20 : ∀ a i,
      CodeReq.singleton (H + 80) (.LI .x10 2) a = some i → cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 80) hvbfProg 20
      (.LI .x10 2) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have h20 := li_spec_gen_own_within .x10 (2 : Word) (H + 80) (by decide)
  have h20' := cpsTripleWithin_extend_code hmem20 h20
  have h20F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (H + 40)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
      (.x11 ↦ᵣ gasUsed) ** (.x0 ↦ᵣ (0 : Word)) **
      tailRest spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) (by pcf; exact hF) h20'
  have h20Epi : cpsTripleWithin 1 (H + 80) (H + 84) cr
      (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfEpiPre spH spK raIn old8 headerPtr (H + 40) (2 : Word) gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) h20F
    · unfold hvbfDispatchPost at hp
      xperm_hyp hp
    · unfold tailRest at hq
      unfold hvbfEpiPre at ⊢
      xperm_hyp hq
  have h20Full := hvbfEpilogue (cr := cr)
    sp0 spH raIn old8 headerPtr (H + 40) (2 : Word) gasUsed gasUsed
    spK v9 v18 v19 v20 parentPtr parentBytes expectedBytes headerBytes F
    hspH hret hcode (by dsimp [F, k74FlatFrame]; pcf; exact hF)
  have hFailPin : cpsTripleWithin 5 (H + 80) raIn cr
      (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfFinal sp0 spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
        (2 : Word) gasUsed parentBytes expectedBytes headerBytes F) := by
    have h := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      unfold hvbfEpiPre at hp
      xperm_hyp hp)
      h20Epi h20Full
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have hFail : cpsTripleWithin 5 (H + 80) raIn cr
      (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfFinalAny sp0 spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hFailPin
    unfold hvbfFinalAny
    exact Or.inl ⟨expectedBytes, hq⟩

  have hFailScratch : ∀ (status : Word) (scratchBytes : List (BitVec 8)),
      status ≠ (0 : Word) →
      cpsTripleWithin 5 (H + 80) raIn cr
        ((.x1 ↦ᵣ (H + 40)) **
          k73FailurePost spH spK headerPtr v9 v18 v19 v20 gasUsed parentPtr
            status parentBytes scratchBytes headerBytes raIn old8 F)
        (hvbfFinal sp0 spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
          (2 : Word) gasUsed parentBytes scratchBytes headerBytes F) := by
    intro status scratchBytes _hstatus
    have h20ScratchF := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ (H + 40)) ** (regIs .x2 spH) ** (regIs .x8 headerPtr) **
        (regIs .x11 gasUsed) ** (regIs .x0 (0 : Word)) **
        tailRestScratch spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
          parentBytes scratchBytes headerBytes F) (by pcf; exact hF) h20'
    have h20Scratch : cpsTripleWithin 1 (H + 80) (H + 84) cr
        ((.x1 ↦ᵣ (H + 40)) **
          k73FailurePost spH spK headerPtr v9 v18 v19 v20 gasUsed parentPtr
            status parentBytes scratchBytes headerBytes raIn old8 F)
        (hvbfEpiPre spH spK raIn old8 headerPtr (H + 40) (2 : Word) gasUsed parentPtr
          v9 v18 v19 v20 parentBytes scratchBytes headerBytes F) := by
      refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => ?_) h20ScratchF
      · have hp' := hp
        unfold k73FailurePost at hp'
        let failureRest : Assertion :=
          (regIs .x1 (H + 40)) ** (regIs .x2 spH) ** (regIs .x8 headerPtr) **
          (regIs .x11 gasUsed) ** (regIs .x0 (0 : Word)) **
          tailRestScratch spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
            parentBytes scratchBytes headerBytes F
        have hreg : ((.x10 ↦ᵣ status) ** failureRest) h := by
          dsimp [failureRest]
          unfold tailRestScratch at hp' ⊢
          dsimp [H] at hp' ⊢
          xperm_hyp hp'
        have hown : (regOwn .x10 ** failureRest) h :=
          sepConj_mono_left (regIs_implies_regOwn (r := .x10) (v := status)) h hreg
        dsimp [failureRest] at hown
        unfold tailRestScratch at hown ⊢
        dsimp [H] at hown ⊢
        xperm_hyp hown
      · unfold hvbfEpiPre
        unfold tailRestScratch at hq
        xperm_hyp hq
    have h20FullScratch := hvbfEpilogue (cr := cr)
      sp0 spH raIn old8 headerPtr (H + 40) (2 : Word) gasUsed gasUsed
      spK v9 v18 v19 v20 parentPtr parentBytes scratchBytes headerBytes F
      hspH hret hcode (by dsimp [F, k74FlatFrame]; pcf; exact hF)
    have h := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      unfold hvbfEpiPre at hp
      xperm_hyp hp) h20Scratch h20FullScratch
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

  have hFailureBranch : ∀ (status : Word) (scratchBytes : List (BitVec 8)),
      status ≠ (0 : Word) →
      cpsTripleWithin 6 (H + 40) raIn cr
        ((.x1 ↦ᵣ (H + 40)) **
          k73FailurePost spH spK headerPtr v9 v18 v19 v20 gasUsed parentPtr
            status parentBytes scratchBytes headerBytes raIn old8 F)
        (hvbfFinalAny sp0 spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
          parentBytes expectedBytes headerBytes F) := by
    intro status scratchBytes hstatus
    have hbneRaw := bne_spec_gen_within .x10 .x0 (40 : BitVec 13) status
      (0 : Word) (H + 40)
    have hbneCode := cpsBranchWithin_extend_code hmem10 hbneRaw
    have hbneFrame := cpsBranchWithin_frameR
      ((.x1 ↦ᵣ (H + 40)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
        (regIs .x11 gasUsed) **
        tailRestScratch spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
          parentBytes scratchBytes headerBytes F) (by pcf; exact hF) hbneCode
    have hbneFailure : cpsBranchWithin 1 (H + 40) cr
        ((regIs .x1 (H + 40)) **
          k73FailurePost spH spK headerPtr v9 v18 v19 v20 gasUsed parentPtr
            status parentBytes scratchBytes headerBytes raIn old8 F)
        (H + 80)
        ((regIs .x1 (H + 40)) **
          k73FailurePost spH spK headerPtr v9 v18 v19 v20 gasUsed parentPtr
            status parentBytes scratchBytes headerBytes raIn old8 F **
          ⌜status ≠ (0 : Word)⌝)
        (H + 44)
        ((regIs .x1 (H + 40)) **
          k73FailurePost spH spK headerPtr v9 v18 v19 v20 gasUsed parentPtr
            status parentBytes scratchBytes headerBytes raIn old8 F **
          ⌜status = (0 : Word)⌝) := by
      refine cpsBranchWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_)
        (fun _ hq => ?_) hbneFrame
      · unfold k73FailurePost at hp
        xperm_hyp hp
      · unfold k73FailurePost
        unfold tailRestScratch at hq ⊢
        dsimp [H] at hq ⊢
        xperm_hyp hq
      · unfold k73FailurePost
        unfold tailRestScratch at hq ⊢
        dsimp [H] at hq ⊢
        xperm_hyp hq
    have h_taken : cpsTripleWithin 1 (H + 40) (H + 80) cr
        ((regIs .x1 (H + 40)) **
          k73FailurePost spH spK headerPtr v9 v18 v19 v20 gasUsed parentPtr
            status parentBytes scratchBytes headerBytes raIn old8 F)
        ((regIs .x1 (H + 40)) **
          k73FailurePost spH spK headerPtr v9 v18 v19 v20 gasUsed parentPtr
            status parentBytes scratchBytes headerBytes raIn old8 F) := by
      apply cpsBranchWithin_takenStripPure2 hbneFailure
      intro h hq
      open EvmAsm.Rv64.Tactics in
        extract_pure_deep hq
      exact hstatus hq.1
    have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
      h_taken (hFailScratch status scratchBytes hstatus)
    have hseq' : cpsTripleWithin 6 (H + 40) raIn cr
        ((regIs .x1 (H + 40)) **
          k73FailurePost spH spK headerPtr v9 v18 v19 v20 gasUsed parentPtr
            status parentBytes scratchBytes headerBytes raIn old8 F)
        (hvbfFinalAny sp0 spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
          parentBytes expectedBytes headerBytes F) := by
      refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) hseq
      exact Or.inl ⟨scratchBytes, hq⟩
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hseq'

  have hmem11 : ∀ a i,
      CodeReq.singleton (H + 44) (.MV .x10 .x8) a = some i → cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 44) hvbfProg 11
      (.MV .x10 .x8) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have h11_values : ∀ old10, cpsTripleWithin 1 (H + 44) (H + 48) cr
      ((.x8 ↦ᵣ headerPtr) ** (.x10 ↦ᵣ old10))
      ((.x8 ↦ᵣ headerPtr) ** (.x10 ↦ᵣ headerPtr)) := by
    intro old10
    have hm := mv_spec_gen_within .x10 .x8 headerPtr old10 (H + 44) (by decide)
    exact cpsTripleWithin_extend_code hmem11 hm
  have h11Own : cpsTripleWithin 1 (H + 44) (H + 48) cr
      ((.x8 ↦ᵣ headerPtr) ** regOwn .x10)
      ((.x8 ↦ᵣ headerPtr) ** (.x10 ↦ᵣ headerPtr)) :=
    cpsTripleWithin_of_forall_regIs_to_regOwn
      (nSteps := 1) (entry := H + 44) (r := .x10)
      (P := (.x8 ↦ᵣ headerPtr)) (exit_ := H + 48)
      (Q := (.x8 ↦ᵣ headerPtr) ** (.x10 ↦ᵣ headerPtr)) h11_values
  have h11F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (H + 40)) ** (.x2 ↦ᵣ spH) ** (.x11 ↦ᵣ gasUsed) **
      (.x0 ↦ᵣ (0 : Word)) **
      tailRest spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) (by pcf; exact hF) h11Own
  have h11Done : cpsTripleWithin 1 (H + 44) (H + 48) cr
      (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfEqPrefixPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) h11F
    · unfold hvbfDispatchPost at hp
      xperm_hyp hp
    · unfold hvbfEqPrefixPost at ⊢
      xperm_hyp hq

  have hmem12 : ∀ a i,
      CodeReq.singleton (H + 48)
        (.AUIPC .x11 (laHi GuestAddrs.hvbf_expected
          (GuestAddrs.header_validate_base_fee + 48))) a = some i →
        cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 48) hvbfProg 12
      (.AUIPC .x11 (laHi GuestAddrs.hvbf_expected
        (GuestAddrs.header_validate_base_fee + 48))) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have hmem13 : ∀ a i,
      CodeReq.singleton (H + 52)
        (.ADDI .x11 .x11 (laLo GuestAddrs.hvbf_expected
          (GuestAddrs.header_validate_base_fee + 48))) a = some i →
        cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 52) hvbfProg 13
      (.ADDI .x11 .x11 (laLo GuestAddrs.hvbf_expected
        (GuestAddrs.header_validate_base_fee + 48))) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have hla := EvmAsm.Rv64.la_materialize_within .x11 gasUsed (H + 48) Expected
    (by decide) (by unfold H Expected; decide) hmem12 hmem13
  have hlaF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (H + 40)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
      (.x10 ↦ᵣ headerPtr) ** (.x0 ↦ᵣ (0 : Word)) **
      tailRest spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) (by pcf; exact hF) hla
  have hprefixRaw := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold hvbfEqPrefixPost at hp
    xperm_hyp hp) h11Done hlaF
  have hprefix : cpsTripleWithin 3 (H + 44) (H + 56) cr
      (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      ((.x1 ↦ᵣ (H + 40)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
        eqPre spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
          parentBytes expectedBytes headerBytes F) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) hprefixRaw
    unfold eqPre
    xperm_hyp hq

  have hmem14 : ∀ a i,
      CodeReq.singleton (H + 56)
        (.JAL .x1 (jalOff GuestAddrs.u256_eq
          (GuestAddrs.header_validate_base_fee + 56))) a = some i →
        cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 56) hvbfProg 14
      (.JAL .x1 (jalOff GuestAddrs.u256_eq
        (GuestAddrs.header_validate_base_fee + 56))) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have heqCr := cpsTripleWithin_extend_code heqMono heq
  have heqFramedRaw := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr)) (by pcf) heqCr
  have heqFramed : cpsTripleWithin nEq EqK (H + 56 + 4) cr
      ((.x1 ↦ᵣ (H + 56 + 4)) **
        ((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
          eqPre spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
            parentBytes expectedBytes headerBytes F))
      ((.x1 ↦ᵣ (H + 56 + 4)) **
        ((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
          eqPostOwn spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
            parentBytes expectedBytes headerBytes F)) := by
    rw [show H + 60 = H + 56 + 4 by bv_omega] at heqFramedRaw
    refine cpsTripleWithin_weaken (fun _ hp => by
        unfold eqPre tailRest at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by
        unfold eqPostOwn tailRest at hq ⊢
        xperm_hyp hq) heqFramedRaw
  have heqCallRaw := callWithin_spec (cr := cr)
    (P := (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
      eqPre spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F)
    (Q := (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
      eqPostOwn spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F)
    (H + 56) EqK (H + 40)
      (jalOff GuestAddrs.u256_eq
        (GuestAddrs.header_validate_base_fee + 56)) nEq
    (by exact jalOff_correct_add GuestAddrs.u256_eq
          GuestAddrs.header_validate_base_fee 56 (by decide) (by decide)
          (by decide) (by decide)) hmem14
    (by pcf; exact hF) heqFramed
  have heqAtRaw := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    xperm_hyp hp) hprefix heqCallRaw
  have heqAt0 : cpsTripleWithin (4 + nEq) (H + 44) (H + 60) cr
      (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      ((.x1 ↦ᵣ (H + 60)) **
        ((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
          eqPostOwn spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
            parentBytes expectedBytes headerBytes F)) := by
    have hretEq : H + 56 + 4 = H + 60 := by bv_omega
    have hsteps : 3 + (1 + nEq) = 4 + nEq := by omega
    simpa only [Nat.add_assoc, hretEq, hsteps] using heqAtRaw
  have heqAt : cpsTripleWithin (4 + nEq) (H + 44) (H + 60) cr
      (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) heqAt0
    unfold eqPostOwn tailRest at hq
    unfold hvbfEqDispatchPost tailRest at ⊢
    xperm_hyp hq

  have hmem15 : ∀ a i,
      CodeReq.singleton (H + 60) (.BEQ .x10 .x0 (12 : BitVec 13)) a = some i →
        cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 60) hvbfProg 15
      (.BEQ .x10 .x0 (12 : BitVec 13)) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have hbeq_values : ∀ eqStatus : Word, cpsBranchWithin 1 (H + 60) cr
      ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ eqStatus)) (H + 72)
        ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) (H + 64)
        ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) := by
    intro eqStatus
    have hb := beq_spec_gen_within .x10 .x0 (12 : BitVec 13) eqStatus
      (0 : Word) (H + 60)
    have hb' := cpsBranchWithin_extend_code hmem15 hb
    exact cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun h hq => by
        have hq' := sepConj_strip_pure_end2 h hq
        have hq'' : ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ eqStatus)) h := by
          xperm_hyp hq'
        exact sepConj_mono_right
          (regIs_implies_regOwn (r := .x10) (v := eqStatus)) h hq'')
      (fun h hq => by
        have hq' := sepConj_strip_pure_end2 h hq
        have hq'' : ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ eqStatus)) h := by
          xperm_hyp hq'
        exact sepConj_mono_right
          (regIs_implies_regOwn (r := .x10) (v := eqStatus)) h hq'') hb'
  have hbeqOwn : cpsBranchWithin 1 (H + 60) cr
      ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) (H + 72)
        ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) (H + 64)
        ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) :=
    cpsBranchWithin_of_forall_regIs_to_regOwn
      (nSteps := 1) (entry := H + 60) (r := .x10)
      (P := (.x0 ↦ᵣ (0 : Word)))
      (exit_t := H + 72) (exit_f := H + 64)
      (Q_t := (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10)
      (Q_f := (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10) hbeq_values
  have hbeqFrame := cpsBranchWithin_frameR
    ((.x1 ↦ᵣ (H + 60)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
      (.x11 ↦ᵣ Expected) **
      tailRest spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) (by pcf; exact hF) hbeqOwn
  have hbeq : cpsBranchWithin 1 (H + 60) cr
      (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (H + 72)
        (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
          v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (H + 64)
        (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
          v9 v18 v19 v20 parentBytes expectedBytes headerBytes F) := by
    refine cpsBranchWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_)
      (fun _ hq => ?_) hbeqFrame
    · simp only [hvbfEqDispatchPost, tailRest] at hp ⊢
      xperm_hyp hp
    · simp only [hvbfEqDispatchPost, tailRest] at hq ⊢
      xperm_hyp hq
    · simp only [hvbfEqDispatchPost, tailRest] at hq ⊢
      xperm_hyp hq

  have hmem18 : ∀ a i,
      CodeReq.singleton (H + 72) (.LI .x10 1) a = some i → cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 72) hvbfProg 18
      (.LI .x10 1) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have h18 := li_spec_gen_own_within .x10 (1 : Word) (H + 72) (by decide)
  have h18' := cpsTripleWithin_extend_code hmem18 h18
  have h18F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (H + 60)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
      (.x11 ↦ᵣ Expected) ** (.x0 ↦ᵣ (0 : Word)) **
      tailRest spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) (by pcf; exact hF) h18'
  have h18Epi : cpsTripleWithin 1 (H + 72) (H + 76) cr
      (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfEpiPre spH spK raIn old8 headerPtr (H + 60) (1 : Word) Expected parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) h18F
    · simp only [hvbfEqDispatchPost, tailRest] at hp ⊢
      xperm_hyp hp
    · simp only [hvbfEpiPre, tailRest] at hq ⊢
      xperm_hyp hq
  have hmem19 : ∀ a i,
      CodeReq.singleton (H + 76) (.JAL .x0 (8 : BitVec 21)) a = some i →
        cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 76) hvbfProg 19
      (.JAL .x0 (8 : BitVec 21)) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have h19 := jal_x0_spec_gen_within (8 : BitVec 21) (H + 76)
  have h19' := cpsTripleWithin_extend_code hmem19 h19
  have h19F := cpsTripleWithin_frameR
    (hvbfEpiPre spH spK raIn old8 headerPtr (H + 60) (1 : Word) Expected parentPtr
      v9 v18 v19 v20 parentBytes expectedBytes headerBytes F) (by pcf; exact hF) h19'
  have hThenEpi : cpsTripleWithin 2 (H + 72) (H + 84) cr
      (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfEpiPre spH spK raIn old8 headerPtr (H + 60) (1 : Word) Expected parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F) := by
    have h := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simpa only [sepConj_emp_left'] using hp) h18Epi h19F
    have hpc : H + 76 + signExtend21 (8 : BitVec 21) = H + 84 := by
      have hs : signExtend21 (8 : BitVec 21) = (8 : Word) := by decide
      rw [hs]
      bv_omega
    rw [hpc] at h
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) h
    simpa only [sepConj_emp_left'] using hq
  have hEpi1 := hvbfEpilogue (cr := cr)
    sp0 spH raIn old8 headerPtr (H + 60) (1 : Word) Expected gasUsed
    spK v9 v18 v19 v20 parentPtr parentBytes expectedBytes headerBytes F
    hspH hret hcode (by dsimp [F, k74FlatFrame]; pcf; exact hF)
  have hThenPin : cpsTripleWithin 6 (H + 72) raIn cr
      (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfFinal sp0 spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
        (1 : Word) Expected parentBytes expectedBytes headerBytes F) := by
    have h := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      unfold hvbfEpiPre at hp
      xperm_hyp hp) hThenEpi hEpi1
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have hThen : cpsTripleWithin 6 (H + 72) raIn cr
      (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfFinalAny sp0 spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hThenPin
    unfold hvbfFinalAny
    exact Or.inr (Or.inr hq)

  have hmem16 : ∀ a i,
      CodeReq.singleton (H + 64) (.LI .x10 0) a = some i → cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 64) hvbfProg 16
      (.LI .x10 0) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have h16 := li_spec_gen_own_within .x10 (0 : Word) (H + 64) (by decide)
  have h16' := cpsTripleWithin_extend_code hmem16 h16
  have h16F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (H + 60)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
      (.x11 ↦ᵣ Expected) ** (.x0 ↦ᵣ (0 : Word)) **
      tailRest spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) (by pcf; exact hF) h16'
  have h16Epi : cpsTripleWithin 1 (H + 64) (H + 68) cr
      (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfEpiPre spH spK raIn old8 headerPtr (H + 60) (0 : Word) Expected parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) h16F
    · simp only [hvbfEqDispatchPost, tailRest] at hp ⊢
      xperm_hyp hp
    · simp only [hvbfEpiPre, tailRest] at hq ⊢
      xperm_hyp hq
  have hmem17 : ∀ a i,
      CodeReq.singleton (H + 68) (.JAL .x0 (16 : BitVec 21)) a = some i →
        cr a = some i := by
    intro a i hi
    apply hcode a i
    exact CodeReq.ofProg_mem_at H (H + 68) hvbfProg 17
      (.JAL .x0 (16 : BitVec 21)) (by bv_omega)
      (by rw [hvbf_length]; decide) rfl (by rw [hvbf_length]; decide) a i hi
  have h17 := jal_x0_spec_gen_within (16 : BitVec 21) (H + 68)
  have h17' := cpsTripleWithin_extend_code hmem17 h17
  have h17F := cpsTripleWithin_frameR
    (hvbfEpiPre spH spK raIn old8 headerPtr (H + 60) (0 : Word) Expected parentPtr
      v9 v18 v19 v20 parentBytes expectedBytes headerBytes F) (by pcf; exact hF) h17'
  have hElseEpi : cpsTripleWithin 2 (H + 64) (H + 84) cr
      (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfEpiPre spH spK raIn old8 headerPtr (H + 60) (0 : Word) Expected parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F) := by
    have h := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simpa only [sepConj_emp_left'] using hp) h16Epi h17F
    have hpc : H + 68 + signExtend21 (16 : BitVec 21) = H + 84 := by
      have hs : signExtend21 (16 : BitVec 21) = (16 : Word) := by decide
      rw [hs]
      bv_omega
    rw [hpc] at h
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) h
    simpa only [sepConj_emp_left'] using hq
  have hEpi0 := hvbfEpilogue (cr := cr)
    sp0 spH raIn old8 headerPtr (H + 60) (0 : Word) Expected gasUsed
    spK v9 v18 v19 v20 parentPtr parentBytes expectedBytes headerBytes F
    hspH hret hcode (by dsimp [F, k74FlatFrame]; pcf; exact hF)
  have hElsePin : cpsTripleWithin 6 (H + 64) raIn cr
      (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfFinal sp0 spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
        (0 : Word) Expected parentBytes expectedBytes headerBytes F) := by
    have h := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      unfold hvbfEpiPre at hp
      xperm_hyp hp) hElseEpi hEpi0
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have hElse : cpsTripleWithin 6 (H + 64) raIn cr
      (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfFinalAny sp0 spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hElsePin
    unfold hvbfFinalAny
    exact Or.inr (Or.inl hq)

  have hEqFull : cpsTripleWithin 7 (H + 60) raIn cr
      (hvbfEqDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfFinalAny sp0 spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) := by
    have h := cpsBranchWithin_merge_same_cr hbeq hThen hElse
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have hEqFullAt : cpsTripleWithin (11 + nEq) (H + 44) raIn cr
      (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfFinalAny sp0 spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) := by
    have h := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
      heqAt hEqFull
    have hs : (4 + nEq) + 7 = 11 + nEq := by omega
    simpa only [hs] using h
  have hMerge : cpsTripleWithin (17 + nEq) (H + 40) raIn cr
      (hvbfDispatchPost spH spK raIn old8 headerPtr gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      (hvbfFinalAny sp0 spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) := by
    have h := cpsBranchWithin_merge_two_bounds_same_cr hbne hFail hEqFullAt
    have hs : 1 + 5 + (11 + nEq) = 17 + nEq := by omega
    simpa only [hs] using h
  have hSuccessMerge : cpsTripleWithin (17 + nEq) (H + 40) raIn cr
      ((regIs .x1 (H + 40)) **
        k73PostOwn spH spK headerPtr v9 v18 v19 v20 gasUsed parentPtr
          parentBytes expectedBytes headerBytes raIn old8 F)
      (hvbfFinalAny sp0 spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => hq) hMerge
    unfold hvbfDispatchPost at ⊢
    dsimp [k73PostOwn] at hp ⊢
    xperm_chunked hp
  have hMergeAny : cpsTripleWithin (17 + nEq) (H + 40) raIn cr
      ((regIs .x1 (H + 40)) **
        k73CallPost spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
          parentBytes expectedBytes headerBytes F)
      (hvbfFinalAny sp0 spH spK raIn old8 headerPtr v9 v18 v19 v20 gasUsed parentPtr
        parentBytes expectedBytes headerBytes F) := by
    intro R hR s hcr hPR hpc
    obtain ⟨h, hcompat, hP_R⟩ := hPR
    obtain ⟨h1, h2, hd, hunion, hP, hR_⟩ := hP_R
    obtain ⟨h1P, h2P, hdP, hunionP, hx1, hK⟩ := hP
    unfold k73CallPost at hK
    rcases hK with hsuccess | ⟨status, scratchBytes, hstatus, hfailure⟩
    · have hP' :
          ((regIs .x1 (H + 40)) **
            k73PostOwn spH spK headerPtr v9 v18 v19 v20 gasUsed parentPtr
              parentBytes expectedBytes headerBytes raIn old8 F) h1 := by
        exact ⟨h1P, h2P, hdP, hunionP, hx1, hsuccess⟩
      have hpre :
          (((regIs .x1 (H + 40)) **
            k73PostOwn spH spK headerPtr v9 v18 v19 v20 gasUsed parentPtr
              parentBytes expectedBytes headerBytes raIn old8 F) ** R) h := by
        exact ⟨h1, h2, hd, hunion, hP', hR_⟩
      have hpreS :
          (((regIs .x1 (H + 40)) **
            k73PostOwn spH spK headerPtr v9 v18 v19 v20 gasUsed parentPtr
              parentBytes expectedBytes headerBytes raIn old8 F) ** R).holdsFor s := by
        exact ⟨h, hcompat, hpre⟩
      exact hSuccessMerge R hR s hcr hpreS hpc
    · have hP' :
          ((regIs .x1 (H + 40)) **
            k73FailurePost spH spK headerPtr v9 v18 v19 v20 gasUsed parentPtr
              status parentBytes scratchBytes headerBytes raIn old8 F) h1 := by
        exact ⟨h1P, h2P, hdP, hunionP, hx1, hfailure⟩
      have hpre :
          (((regIs .x1 (H + 40)) **
            k73FailurePost spH spK headerPtr v9 v18 v19 v20 gasUsed parentPtr
              status parentBytes scratchBytes headerBytes raIn old8 F) ** R) h := by
        exact ⟨h1, h2, hd, hunion, hP', hR_⟩
      have hpreS :
          (((regIs .x1 (H + 40)) **
            k73FailurePost spH spK headerPtr v9 v18 v19 v20 gasUsed parentPtr
              status parentBytes scratchBytes headerBytes raIn old8 F) ** R).holdsFor s := by
        exact ⟨h, hcompat, hpre⟩
      obtain ⟨k, hk, s', hstep, hpc', hQR⟩ :=
        hFailureBranch status scratchBytes hstatus R hR s hcr hpreS hpc
      exact ⟨k, by omega, s', hstep, hpc', hQR⟩
  have hAll := cpsTripleWithin_seq_same_cr hcall hMergeAny
  have hs : (10 + n73) + (17 + nEq) = 27 + n73 + nEq := by omega
  simpa only [F, k74FlatFrame, hs] using hAll


end EvmAsm.Codegen.HeaderValidateBaseFeeSpec
