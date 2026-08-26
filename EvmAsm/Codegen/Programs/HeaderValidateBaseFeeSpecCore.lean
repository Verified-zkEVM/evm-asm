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
import EvmAsm.Rv64.SAsm.AssertionSpec

namespace EvmAsm.Codegen.HeaderValidateBaseFeeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec

abbrev H : Word := (GuestAddrs.header_validate_base_fee : Word)
abbrev K73 : Word := (GuestAddrs.eip1559_calc_base_fee_per_gas : Word)
abbrev EqK : Word := (GuestAddrs.u256_eq : Word)
abbrev hvbfProg : Program := EvmAsm.Codegen.headerValidateBaseFee_prog
abbrev hvbfCode : CodeReq := CodeReq.ofProg H hvbfProg
abbrev u256EqCode : CodeReq := CodeReq.ofProg EqK EvmAsm.Codegen.u256Eq_prog

abbrev Expected : Word := (GuestAddrs.hvbf_expected : Word)

def u256EqRegs : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x12, .x13, .x14, .x15, .x16, .x17]

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
    (_spH spK _raIn _old8 headerPtr v9 old18 _target v19 v20 _gasUsed parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (F : Assertion) :
    Assertion :=
  (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
  regOwn .x12 ** regOwn .x13 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 **
  frameSlotsSaved k73Frame spK
    (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
  bytesRegion headerPtr headerBytes ** bytesRegion parentPtr parentBytes **
  bytesRegion Expected expectedBytes ** F

def tailRest
    (spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (F : Assertion) :
    Assertion :=
  frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
  tailRestCore spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

/-! The K73 failure path is allowed to overwrite the caller-owned expected
    buffer before returning a nonzero status.  Keep that written image in the
    post rather than weakening it to `regOwn`: the next consumer may need the
    bytes, and the whole-routine K73 triple must describe the actual write. -/
def tailRestScratch
    (spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr : Word)
    (parentBytes scratchBytes headerBytes : List (BitVec 8)) (F : Assertion) :
    Assertion :=
  frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
  tailRestCore spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
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
    (spH spK headerPtr v9 old18 target v19 v20 gasUsed parentPtr status : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (raIn old8 : Word) (F : Assertion) : Assertion :=
  (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) ** (.x10 ↦ᵣ status) **
  regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  tailRest spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

def k73PostOwn
    (spH spK headerPtr v9 old18 target v19 v20 gasUsed parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (raIn old8 : Word) (F : Assertion) : Assertion :=
  (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) ** regOwn .x10 **
  regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  tailRest spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

def k73FailurePost
    (spH spK headerPtr v9 old18 target v19 v20 gasUsed parentPtr status : Word)
    (parentBytes scratchBytes headerBytes : List (BitVec 8))
    (raIn old8 : Word) (F : Assertion) : Assertion :=
  (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) ** (.x10 ↦ᵣ status) **
  regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  tailRestScratch spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
    parentBytes scratchBytes headerBytes F

/-! The normalized K73 post consumed by K74.  The successful arm is the
    established fixed-byte post; the failure arm retains both the nonzero
    status and the bytes actually left in the shared output window. -/
def k73CallPost
    (spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (F : Assertion) :
    Assertion := fun h =>
  k73PostOwn spH spK headerPtr v9 old18 target v19 v20 gasUsed parentPtr
      parentBytes expectedBytes headerBytes raIn old8 F h ∨
  ∃ status scratchBytes,
    status ≠ (0 : Word) ∧
    k73FailurePost spH spK headerPtr v9 old18 target v19 v20 gasUsed parentPtr status
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
    (spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  (.x10 ↦ᵣ headerPtr) ** (.x11 ↦ᵣ Expected) ** (.x0 ↦ᵣ (0 : Word)) **
  tailRest spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

def eqPost
    (spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr eqStatus : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  (.x10 ↦ᵣ eqStatus) ** (.x11 ↦ᵣ Expected) ** (.x0 ↦ᵣ (0 : Word)) **
  tailRest spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

def eqPostAny
    (spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (F : Assertion) : Assertion := fun h =>
  ∃ eqStatus,
    eqPost spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr eqStatus
      parentBytes expectedBytes headerBytes F h

def eqPostOwn
    (spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  regOwn .x10 ** (.x11 ↦ᵣ Expected) ** (.x0 ↦ᵣ (0 : Word)) **
  tailRest spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

def k73PostAny
    (spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (F : Assertion) : Assertion := fun h =>
  ∃ status,
    k73PostRest spH spK headerPtr v9 old18 target v19 v20 gasUsed parentPtr status
      parentBytes expectedBytes headerBytes raIn old8 F h

def hvbfFinal
    (sp0 spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
      status out11 : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ old8) **
  (.x10 ↦ᵣ status) ** (.x11 ↦ᵣ out11) ** (.x0 ↦ᵣ (0 : Word)) **
  tailRest spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

def hvbfFinalScratch
    (sp0 spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
      status _out11 : Word)
    (parentBytes scratchBytes headerBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ old8) **
  (.x10 ↦ᵣ status) ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  tailRestScratch spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
    parentBytes scratchBytes headerBytes F

def hvbfFinalAny
    (sp0 spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (F : Assertion) : Assertion := fun h =>
  (∃ scratchBytes,
    hvbfFinalScratch sp0 spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed
      parentPtr (2 : Word) gasUsed parentBytes scratchBytes headerBytes F h) ∨
    hvbfFinal sp0 spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
      (0 : Word) Expected parentBytes expectedBytes headerBytes F h ∨
    hvbfFinal sp0 spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
      (1 : Word) Expected parentBytes expectedBytes headerBytes F h

def hvbfFinalOwn
    (sp0 spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ old8) ** regOwn .x10 **
  regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  tailRest spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

def hvbfDispatchPost
    (spH spK raIn old8 headerPtr gasUsed parentPtr : Word)
    (v9 old18 target v19 v20 : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (F : Assertion) :
    Assertion :=
  (.x1 ↦ᵣ (H + 40)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
  regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  tailRest spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

def hvbfEqDispatchPost
    (spH spK raIn old8 headerPtr gasUsed parentPtr : Word)
    (v9 old18 target v19 v20 : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (F : Assertion) :
    Assertion :=
  (.x1 ↦ᵣ (H + 60)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
  regOwn .x10 ** (.x11 ↦ᵣ Expected) ** (.x0 ↦ᵣ (0 : Word)) **
  tailRest spH spK raIn old8 headerPtr
    v9 old18 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

def hvbfEpiPre
    (spH spK raIn old8 headerPtr raBefore status gasUsed parentPtr : Word)
    (v9 old18 target v19 v20 : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (F : Assertion) :
    Assertion :=
  (.x1 ↦ᵣ raBefore) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
  (.x10 ↦ᵣ status) ** (.x11 ↦ᵣ gasUsed) ** (.x0 ↦ᵣ (0 : Word)) **
  frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
  tailRestCore spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
    parentBytes expectedBytes headerBytes F

def hvbfEpiPreScratch
    (spH spK raIn old8 headerPtr raBefore status gasUsed parentPtr : Word)
    (v9 old18 target v19 v20 : Word)
    (parentBytes scratchBytes headerBytes : List (BitVec 8)) (F : Assertion) :
    Assertion :=
  (.x1 ↦ᵣ raBefore) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
  (.x10 ↦ᵣ status) ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
  tailRestCore spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
    parentBytes scratchBytes headerBytes F

def hvbfEqPrefixPost
    (spH spK raIn old8 headerPtr gasUsed parentPtr : Word)
    (v9 old18 target v19 v20 : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (F : Assertion) :
    Assertion :=
  (.x1 ↦ᵣ (H + 40)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
  (.x10 ↦ᵣ headerPtr) ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  tailRest spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
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

/-! The `u256_eq` call is a small leaf, but its public `Fn` contract is
    expressed through `asrtM` and a whole register file.  K74 needs the
    stronger flat form at the call seam: the two pointer registers are
    explicit, the untouched exposed registers are owned, and the equality
    result is owned rather than fixed.  This adapter is deliberately kept
    here, beside the K74 contract, so the linked `u256_eq` image and its
    `u256EqBody_flatten` bridge are visible in one proof. -/

theorem header_validate_base_fee_eq_leaf_spec_within
    {cr : CodeReq}
    (headerPtr : Word) (headerBytes expectedBytes : List (BitVec 8))
    (hEqMono : ∀ a i, u256EqCode a = some i → cr a = some i)
    (hHeaderWf : (Region.mk headerPtr headerBytes).wf)
    (hExpectedWf : (Region.mk Expected expectedBytes).wf)
    (hHeaderLen : headerBytes.length = 32)
    (hExpectedLen : expectedBytes.length = 32)
    (hDisj : headerPtr.toNat + 32 ≤ Expected.toNat ∨
      Expected.toNat + 32 ≤ headerPtr.toNat) :
    cpsTripleWithin
      (U256EqSAsm.u256EqBody headerPtr Expected headerBytes expectedBytes).steps
      EqK (H + 60) cr
      (((.x1 : Reg) ↦ᵣ (H + 60)) **
        ((.x10 ↦ᵣ headerPtr) ** (.x11 ↦ᵣ Expected) **
          regOwns u256EqRegs ** bytesRegion headerPtr headerBytes **
          bytesRegion Expected expectedBytes))
      (((.x1 : Reg) ↦ᵣ (H + 60)) **
        ((regOwn .x10) ** (.x11 ↦ᵣ Expected) **
          bytesRegion headerPtr headerBytes ** bytesRegion Expected expectedBytes **
          regOwns u256EqRegs)) := by
  have hHeaderBound : headerPtr.toNat + 32 < 2 ^ 64 := by
    have h := hHeaderWf.2.1
    change headerPtr.toNat + headerBytes.length < 2 ^ 64 at h
    omega
  have hExpectedBound : Expected.toNat + 32 < 2 ^ 64 := by
    have h := hExpectedWf.2.1
    change Expected.toNat + expectedBytes.length < 2 ^ 64 at h
    omega
  have hbody :
      (U256EqSAsm.u256EqBody headerPtr Expected headerBytes expectedBytes).flatten EqK =
        EvmAsm.Codegen.u256Eq_prog :=
    U256EqSAsm.u256EqBody_flatten guestLayout headerPtr Expected EqK
      headerBytes expectedBytes
  have hcode : ∀ a i,
      CodeReq.ofProg EqK
          ((U256EqSAsm.u256EqBody headerPtr Expected headerBytes expectedBytes).flatten EqK)
          a = some i → cr a = some i := by
    intro a i hi
    apply hEqMono a i
    change CodeReq.ofProg EqK EvmAsm.Codegen.u256Eq_prog a = some i
    rw [← hbody]
    exact hi
  have h0 := U256EqSAsm.u256Eq_spec headerPtr Expected EqK (H + 60)
    headerBytes expectedBytes (by decide) hHeaderWf hExpectedWf
  have h1 := cpsTripleWithin_extend_code hcode h0
  have hExact : ∀ rf : RegFile,
      U256EqSAsm.u256EqPre headerPtr Expected headerBytes expectedBytes
        rf [] (bytesRegion Expected expectedBytes) →
      cpsTripleWithin
        (U256EqSAsm.u256EqBody headerPtr Expected headerBytes expectedBytes).steps
        EqK (H + 60) cr
        (((.x1 : Reg) ↦ᵣ (H + 60)) **
          (regFileIs rf ** (bytesRegion headerPtr headerBytes **
            bytesRegion Expected expectedBytes)))
        (((.x1 : Reg) ↦ᵣ (H + 60)) **
          asrtM (Region.mk headerPtr headerBytes) RwRegion.empty
            (U256EqSAsm.u256EqPost headerPtr Expected headerBytes expectedBytes)) := by
    intro rf hpre
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq) h1
    unfold asrtM asrtOf
    have hsrc :
        ((.x1 ↦ᵣ (H + 60)) **
          ((regFileIs rf ** bytesRegion Expected expectedBytes) **
            bytesRegion headerPtr headerBytes)) h := by
      xperm_hyp hp
    refine sepConj_mono_right (fun hright hrightp => ?_) h hsrc
    refine sepConj_mono_left (fun hleft hleftp => ?_) hright hrightp
    refine ⟨rf, [], bytesRegion Expected expectedBytes, rfl,
      bytesRegion_pcFree _ _, hpre, ?_⟩
    rw [show bytesRegion RwRegion.empty.base [] = empAssertion from rfl,
      sepConj_emp_right']
    exact hleftp
  let P : Assertion :=
    (.x1 ↦ᵣ (H + 60)) **
      ((.x10 ↦ᵣ headerPtr) ** (.x11 ↦ᵣ Expected) **
        bytesRegion headerPtr headerBytes ** bytesRegion Expected expectedBytes)
  let Ppost : Assertion :=
    (.x1 ↦ᵣ (H + 60)) **
      (regOwn .x10 ** (.x11 ↦ᵣ Expected) **
        bytesRegion headerPtr headerBytes ** bytesRegion Expected expectedBytes **
        regOwns u256EqRegs)
  have hFamily : ∀ vf : Reg → Word,
      cpsTripleWithin
        (U256EqSAsm.u256EqBody headerPtr Expected headerBytes expectedBytes).steps
        EqK (H + 60) cr
        (P ** regAtomsOf vf u256EqRegs) Ppost := by
    intro vf
    let rf : RegFile := fun r =>
      if r = .x10 then headerPtr else if r = .x11 then Expected else vf r
    have hpre : U256EqSAsm.u256EqPre headerPtr Expected headerBytes expectedBytes
        rf [] (bytesRegion Expected expectedBytes) := by
      unfold U256EqSAsm.u256EqPre
      have h10 : rf.get .x10 = headerPtr := by rfl
      have h11 : rf.get .x11 = Expected := by rfl
      exact ⟨h10, h11, hHeaderLen, hExpectedLen, hHeaderBound,
        hExpectedBound, hDisj, rfl⟩
    have hexact := hExact rf hpre
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hexact
    · dsimp [P, u256EqRegs] at hp ⊢
      rw [regFileIs_eq_atoms]
      have hrf5 : rf.get .x5 = vf .x5 := by simp [rf, RegFile.get]
      have hrf6 : rf.get .x6 = vf .x6 := by simp [rf, RegFile.get]
      have hrf7 : rf.get .x7 = vf .x7 := by simp [rf, RegFile.get]
      have hrf28 : rf.get .x28 = vf .x28 := by simp [rf, RegFile.get]
      have hrf29 : rf.get .x29 = vf .x29 := by simp [rf, RegFile.get]
      have hrf30 : rf.get .x30 = vf .x30 := by simp [rf, RegFile.get]
      have hrf31 : rf.get .x31 = vf .x31 := by simp [rf, RegFile.get]
      have hrf10 : rf.get .x10 = headerPtr := by simp [rf, RegFile.get]
      have hrf11 : rf.get .x11 = Expected := by simp [rf, RegFile.get]
      have hrf12 : rf.get .x12 = vf .x12 := by simp [rf, RegFile.get]
      have hrf13 : rf.get .x13 = vf .x13 := by simp [rf, RegFile.get]
      have hrf14 : rf.get .x14 = vf .x14 := by simp [rf, RegFile.get]
      have hrf15 : rf.get .x15 = vf .x15 := by simp [rf, RegFile.get]
      have hrf16 : rf.get .x16 = vf .x16 := by simp [rf, RegFile.get]
      have hrf17 : rf.get .x17 = vf .x17 := by simp [rf, RegFile.get]
      rw [hrf5, hrf6, hrf7, hrf28, hrf29, hrf30, hrf31, hrf10, hrf11,
        hrf12, hrf13, hrf14, hrf15, hrf16, hrf17] at ⊢
      rw [sepConj_emp_right'] at hp
      let src : Assertion :=
        (((Reg.x1 ↦ᵣ H + 60) ** (Reg.x10 ↦ᵣ headerPtr) **
            (Reg.x11 ↦ᵣ Expected) ** bytesRegion headerPtr headerBytes **
              bytesRegion Expected expectedBytes) **
          (Reg.x5 ↦ᵣ vf .x5) ** (Reg.x6 ↦ᵣ vf .x6) ** (Reg.x7 ↦ᵣ vf .x7) **
            (Reg.x28 ↦ᵣ vf .x28) ** (Reg.x29 ↦ᵣ vf .x29) **
              (Reg.x30 ↦ᵣ vf .x30) ** (Reg.x31 ↦ᵣ vf .x31) **
                (Reg.x12 ↦ᵣ vf .x12) ** (Reg.x13 ↦ᵣ vf .x13) **
                  (Reg.x14 ↦ᵣ vf .x14) ** (Reg.x15 ↦ᵣ vf .x15) **
                    (Reg.x16 ↦ᵣ vf .x16) ** (Reg.x17 ↦ᵣ vf .x17))
      let dst : Assertion :=
        ((Reg.x1 ↦ᵣ H + 60) **
          ((Reg.x5 ↦ᵣ vf .x5) ** (Reg.x6 ↦ᵣ vf .x6) ** (Reg.x7 ↦ᵣ vf .x7) **
            (Reg.x28 ↦ᵣ vf .x28) ** (Reg.x29 ↦ᵣ vf .x29) **
              (Reg.x30 ↦ᵣ vf .x30) ** (Reg.x31 ↦ᵣ vf .x31) **
                (Reg.x10 ↦ᵣ headerPtr) ** (Reg.x11 ↦ᵣ Expected) **
                  (Reg.x12 ↦ᵣ vf .x12) ** (Reg.x13 ↦ᵣ vf .x13) **
                    (Reg.x14 ↦ᵣ vf .x14) ** (Reg.x15 ↦ᵣ vf .x15) **
                      (Reg.x16 ↦ᵣ vf .x16) ** (Reg.x17 ↦ᵣ vf .x17)) **
            (bytesRegion headerPtr headerBytes ** bytesRegion Expected expectedBytes))
      change src h at hp
      change dst h
      have hpperm : src = dst := by
        dsimp [src, dst]
        xperm
      exact (congrFun hpperm h).mp hp
    · unfold asrtM at hq
      refine sepConj_mono_right (fun hright hrightp => ?_) h hq
      have hmapped :
          ((regOwn .x10 ** (.x11 ↦ᵣ Expected) **
              bytesRegion Expected expectedBytes ** regOwns u256EqRegs) **
            bytesRegion headerPtr headerBytes) hright := by
        refine sepConj_mono_left (fun hleft hleftp => ?_) hright hrightp
        obtain ⟨rfPost, wsPost, APost, hwsPost, hApcPost, hpostPost,
          hstatePost⟩ := hleftp
        have hws0 : wsPost = [] := by
          apply List.eq_nil_of_length_eq_zero
          simpa [RwRegion.empty] using hwsPost
        subst wsPost
        unfold U256EqSAsm.u256EqPost at hpostPost
        obtain ⟨hx10Post, hx11Post, hlen1Post, hlen2Post, hbound1Post,
          hbound2Post, hAeqPost⟩ := hpostPost
        rw [hAeqPost] at hstatePost
        rw [show bytesRegion RwRegion.empty.base [] = empAssertion from rfl,
          sepConj_emp_right'] at hstatePost
        rw [regFileIs_eq_atoms] at hstatePost
        have hstateMap :
            ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
                regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x10 **
                  (.x11 ↦ᵣ Expected) ** regOwn .x12 ** regOwn .x13 **
                    regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17) **
              bytesRegion Expected expectedBytes) hleft := by
          refine sepConj_mono_left (fun hregs hregsPost => ?_) hleft hstatePost
          refine (sepConj_mono (regIs_to_regOwn .x5 _) ?_) hregs hregsPost
          refine sepConj_mono (regIs_to_regOwn .x6 _) ?_
          refine sepConj_mono (regIs_to_regOwn .x7 _) ?_
          refine sepConj_mono (regIs_to_regOwn .x28 _) ?_
          refine sepConj_mono (regIs_to_regOwn .x29 _) ?_
          refine sepConj_mono (regIs_to_regOwn .x30 _) ?_
          refine sepConj_mono (regIs_to_regOwn .x31 _) ?_
          refine sepConj_mono (regIs_to_regOwn .x10 _) ?_
          refine sepConj_mono (fun _ hp => by simpa [hx11Post] using hp) ?_
          refine sepConj_mono (regIs_to_regOwn .x12 _) ?_
          refine sepConj_mono (regIs_to_regOwn .x13 _) ?_
          refine sepConj_mono (regIs_to_regOwn .x14 _) ?_
          refine sepConj_mono (regIs_to_regOwn .x15 _) ?_
          refine sepConj_mono (regIs_to_regOwn .x16 _) ?_
          exact regIs_to_regOwn .x17 _
        have htarget :
            (regOwn .x10 ** (.x11 ↦ᵣ Expected) **
              bytesRegion Expected expectedBytes ** regOwns u256EqRegs) hleft := by
          simp [u256EqRegs, regOwns] at hstateMap ⊢
          rw [sepConj_emp_right'] at ⊢
          xperm_hyp hstateMap
        exact htarget
      xperm_hyp hmapped
  have hOwn := cpsTripleWithin_peel_regOwns u256EqRegs (by decide) hFamily
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hOwn
  · dsimp [P, u256EqRegs] at hp ⊢
    xperm_hyp hp
  · dsimp [Ppost, u256EqRegs] at hq ⊢
    xperm_hyp hq

theorem header_validate_base_fee_eq_call_spec_within
    {cr : CodeReq}
    (spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hHeaderWf : (Region.mk headerPtr headerBytes).wf)
    (hExpectedWf : (Region.mk Expected expectedBytes).wf)
    (hHeaderLen : headerBytes.length = 32)
    (hExpectedLen : expectedBytes.length = 32)
    (hDisj : headerPtr.toNat + 32 ≤ Expected.toNat ∨
      Expected.toNat + 32 ≤ headerPtr.toNat)
    (heqMono : ∀ a i, u256EqCode a = some i → cr a = some i) :
    cpsTripleWithin
      (U256EqSAsm.u256EqBody headerPtr Expected headerBytes expectedBytes).steps
      EqK (H + 60) cr
      ((.x1 ↦ᵣ (H + 60)) **
        eqPre spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
          parentBytes expectedBytes headerBytes (k74FlatFrame F))
      ((.x1 ↦ᵣ (H + 60)) **
        eqPostOwn spH spK raIn old8 headerPtr v9 old18 target v19 v20 gasUsed parentPtr
          parentBytes expectedBytes headerBytes (k74FlatFrame F)) := by
  let Freq : Assertion :=
    (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ old18) **
    (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
    frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
    frameSlotsSaved k73Frame spK (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
    bytesRegion parentPtr parentBytes ** F
  have hleaf := header_validate_base_fee_eq_leaf_spec_within (cr := cr)
    headerPtr headerBytes expectedBytes heqMono hHeaderWf hExpectedWf
    hHeaderLen hExpectedLen hDisj
  have hframe := cpsTripleWithin_frameR Freq (by pcf; exact hF) hleaf
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hframe
  · unfold eqPre tailRest tailRestCore k74FlatFrame at hp
    unfold Freq
    simp [u256EqRegs, regOwns] at hp ⊢
    xperm_hyp hp
  · unfold Freq at hq
    unfold eqPostOwn tailRest tailRestCore k74FlatFrame
    simp [u256EqRegs, regOwns] at hq ⊢
    xperm_hyp hq

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
        k73CallPost spH spK raIn old8 headerPtr v9 v18 (gasLimit >>> 1) v19 v20
          gasUsed parentPtr parentBytes expectedBytes headerBytes F)) :
    cpsTripleWithin (10 + n) H (H + 40) cr
      (hvbfPre sp0 spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr
        v9 v18 v19 v20 parentBytes expectedBytes headerBytes F)
      ((.x1 ↦ᵣ (H + 40)) **
        k73CallPost spH spK raIn old8 headerPtr v9 v18 (gasLimit >>> 1) v19 v20
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
    (Q := k73CallPost spH spK raIn old8 headerPtr v9 v18 (gasLimit >>> 1) v19 v20
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

end EvmAsm.Codegen.HeaderValidateBaseFeeSpec
