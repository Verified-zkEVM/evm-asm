/-
  EvmAsm.Codegen.Programs.ValidateHeaderGasCorrespondence

  Call-site adapters for conjuncts 2 and 4 of `validate_header`:

  * `header_validate_excess_blob_gas` at `validate_header + 80` (K70), and
  * `header_validate_base_fee` at `validate_header + 132` (K74).

  Neither callee currently has a top-level machine triple.  The adapters
  therefore retain those triples as explicit premises.  This is intentional:
  K74 depends on K73 `eip1559_calc_base_fee_per_gas`, whose `u256_mul_u64_be`
  dependency currently has component proofs only (the MUL gap is downstream
  bookkeeping for this adapter, not a reason to pretend K74 is proved).
-/

import EvmAsm.Codegen.Programs.ValidateHeaderCorrespondence
import EvmAsm.Codegen.Programs.HeaderBaseFee
import EvmAsm.Rv64.SAsm.AbiFrameCall

namespace EvmAsm.Codegen.ValidateHeaderGasCorrespondence

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

abbrev H : Word := EvmAsm.Codegen.ValidateHeaderCorrespondence.H
abbrev callerCode : CodeReq := EvmAsm.Codegen.ValidateHeaderCorrespondence.callerCode

abbrev ExcessA : Word := H + 80
abbrev ExcessRet : Word := H + 84
abbrev ExcessK : Word := (GuestAddrs.header_validate_excess_blob_gas : Word)

abbrev BaseA : Word := H + 132
abbrev BaseRet : Word := H + 136
abbrev BaseK : Word := (GuestAddrs.header_validate_base_fee : Word)

def excessFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32),
   (.x20, 40), (.x21, 48)]

def excessSavedFrame : FrameDesc :=
  [(.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40), (.x21, 48)]

def excessFrameVals (ret : Word) (vals : Reg → Word) : Reg → Word :=
  fun r => if r = .x1 then ret else vals r

def excessEntryRest
    (sp0 : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 : Word) (scratch : Assertion) : Assertion :=
  (.x2 ↦ᵣ sp0) **
  frameSlotsOwn excessFrame (sp0 + signExtend12 (-64 : BitVec 12)) **
  regsAt excessSavedFrame vals **
  (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
  regOwns [.x5, .x6, .x28, .x29, .x30, .x31] **
  (.x0 ↦ᵣ (0 : Word)) ** scratch

def excessCalleePost
    (sp0 : Word) (vals : Reg → Word) (status ret : Word)
    (scratchPost : Assertion) : Assertion :=
  (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
  frameSlotsSaved excessFrame (sp0 + signExtend12 (-64 : BitVec 12))
    (excessFrameVals ret vals) **
  regsAt excessSavedFrame vals **
  (.x10 ↦ᵣ status) **
  regOwns [.x5, .x6, .x11, .x12, .x13, .x28, .x29, .x30, .x31] **
  (.x0 ↦ᵣ (0 : Word)) ** scratchPost

def baseFrame : FrameDesc := [(.x1, 0), (.x8, 8)]

def baseSavedFrame : FrameDesc := [(.x8, 8)]

def baseFrameVals (ret : Word) (vals : Reg → Word) : Reg → Word :=
  fun r => if r = .x1 then ret else vals r

def baseEntryRest
    (sp0 : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 : Word) (scratch : Assertion) : Assertion :=
  (.x2 ↦ᵣ sp0) **
  frameSlotsOwn baseFrame (sp0 + signExtend12 (-16 : BitVec 12)) **
  regsAt baseSavedFrame vals **
  (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
  regOwns [.x5, .x6, .x7, .x28, .x29, .x30, .x31] **
  (.x0 ↦ᵣ (0 : Word)) ** scratch

def baseCalleePost
    (sp0 : Word) (vals : Reg → Word) (status ret : Word)
    (scratchPost : Assertion) : Assertion :=
  (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ sp0) **
  frameSlotsSaved baseFrame (sp0 + signExtend12 (-16 : BitVec 12))
    (baseFrameVals ret vals) **
  regsAt baseSavedFrame vals **
  (.x10 ↦ᵣ status) **
  regOwns [.x5, .x6, .x7, .x11, .x12, .x13, .x28, .x29, .x30, .x31] **
  (.x0 ↦ᵣ (0 : Word)) ** scratchPost

theorem excessEntryRest_pcFree
    (sp0 : Word) (vals : Reg → Word) (a0 a1 a2 a3 : Word)
    (scratch : Assertion) (hscratch : scratch.pcFree) :
    (excessEntryRest sp0 vals a0 a1 a2 a3 scratch).pcFree := by
  unfold excessEntryRest excessFrame excessSavedFrame
  pcf
  exact hscratch

theorem baseEntryRest_pcFree
    (sp0 : Word) (vals : Reg → Word) (a0 a1 a2 a3 : Word)
    (scratch : Assertion) (hscratch : scratch.pcFree) :
    (baseEntryRest sp0 vals a0 a1 a2 a3 scratch).pcFree := by
  unfold baseEntryRest baseFrame baseSavedFrame
  pcf
  exact hscratch

theorem excess_jal_mem :
    ∀ a i, CodeReq.singleton ExcessA
      (.JAL .x1 (jalOff GuestAddrs.header_validate_excess_blob_gas
        (GuestAddrs.validate_header + 80))) a = some i → callerCode a = some i := by
  exact CodeReq.ofProg_mem_at
    (GuestAddrs.validate_header : Word) ExcessA EvmAsm.Codegen.validateHeader_prog 20 _
    (by bv_omega) (by rw [EvmAsm.Codegen.ValidateHeaderCorrespondence.validateHeader_length]; decide)
    rfl (by rw [EvmAsm.Codegen.ValidateHeaderCorrespondence.validateHeader_length]; decide)

theorem base_jal_mem :
    ∀ a i, CodeReq.singleton BaseA
      (.JAL .x1 (jalOff GuestAddrs.header_validate_base_fee
        (GuestAddrs.validate_header + 132))) a = some i → callerCode a = some i := by
  exact CodeReq.ofProg_mem_at
    (GuestAddrs.validate_header : Word) BaseA EvmAsm.Codegen.validateHeader_prog 33 _
    (by bv_omega) (by rw [EvmAsm.Codegen.ValidateHeaderCorrespondence.validateHeader_length]; decide)
    rfl (by rw [EvmAsm.Codegen.ValidateHeaderCorrespondence.validateHeader_length]; decide)

theorem excess_target :
    ExcessA + signExtend21 (jalOff GuestAddrs.header_validate_excess_blob_gas
      (GuestAddrs.validate_header + 80)) = ExcessK := by
  change BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 80 + _ =
    BitVec.ofNat 64 GuestAddrs.header_validate_excess_blob_gas
  exact jalOff_correct_add GuestAddrs.header_validate_excess_blob_gas
    GuestAddrs.validate_header 80 (by decide) (by decide) (by decide) (by decide)

theorem base_target :
    BaseA + signExtend21 (jalOff GuestAddrs.header_validate_base_fee
      (GuestAddrs.validate_header + 132)) = BaseK := by
  change BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 132 + _ =
    BitVec.ofNat 64 GuestAddrs.header_validate_base_fee
  exact jalOff_correct_add GuestAddrs.header_validate_base_fee
    GuestAddrs.validate_header 132 (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 8000 in
theorem validate_header_excess_blob_gas_call_spec_within
    {cr calleeCode : CodeReq} {n : Nat}
    (sp0 : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 status oldRa : Word)
    (scratch scratchPost F : Assertion)
    (hscratch : scratch.pcFree) (hF : F.pcFree)
    (hcallerDisj : callerCode.Disjoint calleeCode)
    (hcode : ∀ a i, (callerCode.union calleeCode) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n ExcessK ExcessRet calleeCode
      ((.x1 ↦ᵣ ExcessRet) ** excessEntryRest sp0 vals a0 a1 a2 a3 scratch)
      (excessCalleePost sp0 vals status ExcessRet scratchPost)) :
    cpsTripleWithin (1 + n) ExcessA ExcessRet cr
      (((.x1 ↦ᵣ oldRa) ** excessEntryRest sp0 vals a0 a1 a2 a3 scratch) ** F)
      (excessCalleePost sp0 vals status ExcessRet scratchPost ** F) := by
  have hret : ExcessA + 4 = ExcessRet := by decide
  have hmem : ∀ a i,
      CodeReq.singleton ExcessA
        (.JAL .x1 (jalOff GuestAddrs.header_validate_excess_blob_gas
          (GuestAddrs.validate_header + 80))) a = some i →
      (callerCode.union calleeCode) a = some i := by
    intro a i hi
    exact CodeReq.union_mono_left a i (excess_jal_mem a i hi)
  have hcalleeU := cpsTripleWithin_extend_code
    (CodeReq.mono_union_right hcallerDisj (fun _ _ h => h)) hcallee
  have hcall := callWithin_spec (cr := callerCode.union calleeCode)
    ExcessA ExcessK oldRa
    (jalOff GuestAddrs.header_validate_excess_blob_gas
      (GuestAddrs.validate_header + 80)) n excess_target hmem
    (excessEntryRest_pcFree sp0 vals a0 a1 a2 a3 scratch hscratch) hcalleeU
  have hcallCr := cpsTripleWithin_extend_code hcode hcall
  have hcallF := cpsTripleWithin_frameR F hF hcallCr
  simpa [hret] using hcallF

set_option maxRecDepth 8000 in
theorem validate_header_base_fee_call_spec_within
    {cr calleeCode : CodeReq} {n : Nat}
    (sp0 : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 status oldRa : Word)
    (scratch scratchPost F : Assertion)
    (hscratch : scratch.pcFree) (hF : F.pcFree)
    (hcallerDisj : callerCode.Disjoint calleeCode)
    (hcode : ∀ a i, (callerCode.union calleeCode) a = some i → cr a = some i)
    (hcallee : cpsTripleWithin n BaseK BaseRet calleeCode
      ((.x1 ↦ᵣ BaseRet) ** baseEntryRest sp0 vals a0 a1 a2 a3 scratch)
      (baseCalleePost sp0 vals status BaseRet scratchPost)) :
    cpsTripleWithin (1 + n) BaseA BaseRet cr
      (((.x1 ↦ᵣ oldRa) ** baseEntryRest sp0 vals a0 a1 a2 a3 scratch) ** F)
      (baseCalleePost sp0 vals status BaseRet scratchPost ** F) := by
  have hret : BaseA + 4 = BaseRet := by decide
  have hmem : ∀ a i,
      CodeReq.singleton BaseA
        (.JAL .x1 (jalOff GuestAddrs.header_validate_base_fee
          (GuestAddrs.validate_header + 132))) a = some i →
      (callerCode.union calleeCode) a = some i := by
    intro a i hi
    exact CodeReq.union_mono_left a i (base_jal_mem a i hi)
  have hcalleeU := cpsTripleWithin_extend_code
    (CodeReq.mono_union_right hcallerDisj (fun _ _ h => h)) hcallee
  have hcall := callWithin_spec (cr := callerCode.union calleeCode)
    BaseA BaseK oldRa
    (jalOff GuestAddrs.header_validate_base_fee
      (GuestAddrs.validate_header + 132)) n base_target hmem
    (baseEntryRest_pcFree sp0 vals a0 a1 a2 a3 scratch hscratch) hcalleeU
  have hcallCr := cpsTripleWithin_extend_code hcode hcall
  have hcallF := cpsTripleWithin_frameR F hF hcallCr
  simpa [hret] using hcallF

end EvmAsm.Codegen.ValidateHeaderGasCorrespondence
