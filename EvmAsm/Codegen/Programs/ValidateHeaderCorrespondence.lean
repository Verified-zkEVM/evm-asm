/-
  EvmAsm.Codegen.Programs.ValidateHeaderCorrespondence

  First correspondence slice for the SpecRef-shaped `validate_header` Program
  introduced by #12345.  This file deliberately proves the call-site frame for
  conjunct 7 (`extra_data.length <= 32`) before attempting the other six
  conjuncts.  The caller's preceding checks are still outside this theorem;
  their entry obligations are therefore explicit rather than silently
  discharged by a fabricated whole-routine precondition.

  At `validate_header + 176`, the Program copies the header RLP pointer and
  length to `a0/a1` and calls the already-proven
  `header_validate_extra_data_length` callee.  The theorem below composes that
  linked `jal` with the callee's whole contract and preserves the caller-owned
  frame.  The reference-side decision tie remains
  `header_extra_data_length_of_decode` in
  `HeaderValidateExtraDataLengthBridge.lean`.

  No number/parent-number < 2^64 gate is needed for this conjunct.  Those are
  project assumptions for the later inlined scalar comparisons, not facts
  needed by the extra-data length check.  The callee's alignment, byte-region,
  slack, and non-wrapping hypotheses remain explicit here.
-/

import EvmAsm.Codegen.Programs.ValidateHeader
import EvmAsm.Codegen.Programs.HeaderValidateExtraDataLengthSpec
import EvmAsm.Codegen.Programs.HeaderValidateExtraDataLengthBridge
import EvmAsm.Rv64.SAsm.AbiFrameCall

namespace EvmAsm.Codegen.ValidateHeaderCorrespondence

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

/-! ## Linked code and the call-site frame -/

abbrev H : Word := (GuestAddrs.validate_header : Word)
abbrev A : Word := H + 176
abbrev Ret : Word := H + 180
abbrev Callee : Word :=
  (GuestAddrs.header_validate_extra_data_length : Word)

abbrev callerCode : CodeReq := CodeReq.ofProg H EvmAsm.Codegen.validateHeader_prog

def fullCode : CodeReq :=
  callerCode.union EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec.fullCode

theorem validateHeader_length : EvmAsm.Codegen.validateHeader_prog.length = 97 := by
  decide

/- The frame at the call entry is the callee precondition with the linking
   register removed.  The caller's live `s0/s1/s2/s3` values are carried by
   `saved.s0..saved.s3`; `saved.s4/s5` are the caller's parent RLP pointer and
   length.  `x12/x13/x14` are intentionally arbitrary at this call site: the
   callee overwrites its own field index and output-cell pointers. -/
def extraDataCallFrame
    (sp0 oldRaSlot spH newSp listBase listLenW old12 old13 old14
      oldOffset oldLen : Word) (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ sp0) ** (spH ↦ₘ oldRaSlot) **
  (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ old12) **
  (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14) **
  (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) **
  (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
  (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion listBase bytes **
  frameSlotsOwn EvmAsm.Codegen.RlpListNthItemSAsm.listNthFrame newSp **
  (EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec.Off ↦ₘ oldOffset) **
  (EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec.Len ↦ₘ oldLen)

theorem caller_hved_disjoint :
    callerCode.Disjoint EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec.fullCode := by
  unfold callerCode
    EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec.fullCode
    EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec.hvedCode
    EvmAsm.Codegen.RlpListNthItemSAsm.code
  apply CodeReq.Disjoint.union_right
  · apply CodeReq.Disjoint.ofProg_ranges
    · rw [validateHeader_length]; decide
    · rw [EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec.hved_length]; decide
    · rw [validateHeader_length,
        EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec.hved_length]
      decide
  · apply CodeReq.Disjoint.ofProg_ranges
    · rw [validateHeader_length]; decide
    · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
    · rw [validateHeader_length,
        EvmAsm.Codegen.RlpListNthItemSAsm.total_length]
      decide

theorem caller_mono :
    ∀ a i, callerCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.union_mono_left a i hi

theorem hved_mono :
    ∀ a i, EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec.fullCode a = some i →
      fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right caller_hved_disjoint (fun _ _ h => h) a i hi

/-! ## Conjunct-7 call composition -/

set_option maxRecDepth 8000 in
/-- **Conjunct 7 at the real `validate_header` call site.**

    The entry contract is the caller-owned frame above, plus the linking
    register supplied by `jal`.  The call at `H + 176` is the concrete
    instruction 44 of `validateHeader_prog`; its linked target is
    `header_validate_extra_data_length`.  The post is exactly the callee's
    three-way result, so the reference-side decision can be consumed by
    `header_extra_data_length_of_decode` without inventing a result predicate.

    The only input-domain hypotheses here are those required by the already
    proven callee: 8-byte alignment, byte-access validity, enough caller-owned
    RLP region for K20's strict scanner, and a non-wrapping address range.  In
    particular, this conjunct does not assume a width bound on either header
    number; those are named project-assumption gates for later conjuncts. -/
theorem validate_header_extra_data_length_call_spec_within
    (sp0 oldRa oldRaSlot spH newSp listBase listLenW old12 old13 old14
      oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hnewSp : newSp = spH + signExtend12 (-64 : BitVec 12))
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hraSaved : saved.ra =
      EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec.H + 32) :
    cpsTripleWithin
      (1 + (7 + 1 + EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec.nCall + 11))
      A Ret fullCode
      ((.x1 ↦ᵣ oldRa) **
        extraDataCallFrame sp0 oldRaSlot spH newSp listBase listLenW old12 old13
          old14 oldOffset oldLen saved bytes)
      (EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec.hvedPost
        sp0 spH newSp Ret listBase oldOffset oldLen saved bytes listLen) := by
  have hjal := jal_link_spec_within
    (jalOff GuestAddrs.header_validate_extra_data_length
      (GuestAddrs.validate_header + 176)) A oldRa
  rw [show (H + 176) + signExtend21 (jalOff GuestAddrs.header_validate_extra_data_length
      (GuestAddrs.validate_header + 176)) = Callee from by
        change BitVec.ofNat 64 GuestAddrs.validate_header + BitVec.ofNat 64 176 + _ =
          BitVec.ofNat 64 GuestAddrs.header_validate_extra_data_length
        exact jalOff_correct_add GuestAddrs.header_validate_extra_data_length
          GuestAddrs.validate_header 176 (by decide) (by decide) (by decide) (by decide),
      show (H + 176 + 4 : Word) = Ret from by bv_omega] at hjal
  have hjalC := cpsTripleWithin_extend_code caller_mono
    (cpsTripleWithin_extend_code (cr' := callerCode)
      (CodeReq.ofProg_mem_at H A EvmAsm.Codegen.validateHeader_prog 44
        (.JAL .x1 (jalOff GuestAddrs.header_validate_extra_data_length
          (GuestAddrs.validate_header + 176))) (by bv_omega)
        (by rw [validateHeader_length]; decide) rfl
        (by rw [validateHeader_length]; decide)) hjal)
  have hjalF := cpsTripleWithin_frameR
    (extraDataCallFrame sp0 oldRaSlot spH newSp listBase listLenW old12 old13
      old14 oldOffset oldLen saved bytes) (by unfold extraDataCallFrame; pcf) hjalC
  have hcallee0 :=
    EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec.header_validate_extra_data_length_spec_within
      sp0 Ret oldRaSlot spH newSp listBase listLenW old12 old13 old14 oldOffset oldLen
      saved bytes listLen hspH hnewSp hlistLenW hsalign hslack hover hvalid
      (by decide) hraSaved
  have hcalleeC := cpsTripleWithin_extend_code hved_mono hcallee0
  have hcallee : cpsTripleWithin
      (7 + 1 + EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec.nCall + 11)
      Callee Ret fullCode
      ((.x1 ↦ᵣ Ret) ** extraDataCallFrame sp0 oldRaSlot spH newSp listBase
        listLenW old12 old13 old14 oldOffset oldLen saved bytes)
      (EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec.hvedPost
        sp0 spH newSp Ret listBase oldOffset oldLen saved bytes listLen) := by
    exact cpsTripleWithin_weaken (fun _ hp => by
      unfold EvmAsm.Codegen.HeaderValidateExtraDataLengthSpec.hvedPre at ⊢
      unfold extraDataCallFrame at hp
      xperm_hyp hp) (fun _ hq => hq) hcalleeC
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hjalF hcallee

end EvmAsm.Codegen.ValidateHeaderCorrespondence
