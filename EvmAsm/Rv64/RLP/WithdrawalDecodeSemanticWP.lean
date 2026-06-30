/-
  EvmAsm.Rv64.RLP.WithdrawalDecodeSemanticWP

  Composed semantic WP facade for the withdrawal decoder prefix classifier:
  empty and not-list exits expose the public ABI post, the short-list success
  exit is continued through the generated schema tail, and the long-list exit
  remains open for the next layer.
-/

import EvmAsm.Rv64.RLP.WithdrawalDecodeFailureWP
import EvmAsm.Rv64.RLP.WithdrawalDecodeShortWP

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

namespace WithdrawalDecode

attribute [rv64_wp] prologuePost prologueFrameBase

/-- Schema scratch registers preserved on failure exits after the output bytes
    have been consumed by the public ABI post. -/
def schemaWalkInitRegsFrame (outBase : Word) : Assertion :=
  ((.x8 ↦ᵣ outBase) ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15)

/-- `schemaWalkInitFrame` with its zeroed output buffer weakened to arbitrary
    output ownership. This is the bridge from the success-oriented schema frame
    to reason-erased ABI failure posts. -/
def schemaWalkInitAnyFrame (outBase : Word) : Assertion :=
  ((.x8 ↦ᵣ outBase) ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
    regOwn .x15 ** bytesRegionAny outBase outputSize)

theorem schemaWalkInitFrame_entails_anyFrame (outBase : Word) :
    WP.Entails (schemaWalkInitFrame outBase) (schemaWalkInitAnyFrame outBase) := by
  intro h hp
  unfold schemaWalkInitFrame at hp
  unfold schemaWalkInitAnyFrame
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (fun h hp =>
      ⟨List.replicate outputSize (0 : Byte), by simp [outputSize], hp⟩))))) h hp

/-- Schema handoff frame in the exact shape produced after the decoder prologue:
    `s0`/`x8` and `a2`/`x12` both hold the output pointer.  The public schema
    handoff only needs `regOwn x12`, so this frame is an entry-composition
    helper, not a separate schema requirement. -/
def schemaWalkInitFrameFromPrologue (outBase : Word) : Assertion :=
  ((.x8 ↦ᵣ outBase) ** (.x12 ↦ᵣ outBase) ** regOwn .x13 ** regOwn .x14 **
    regOwn .x15 ** bytesRegion outBase (List.replicate outputSize (0 : Byte)))

theorem schemaWalkInitFrameFromPrologue_pcFree (outBase : Word) :
    (schemaWalkInitFrameFromPrologue outBase).pcFree := by
  unfold schemaWalkInitFrameFromPrologue
  pcFree

theorem schemaWalkInitFrameFromPrologue_entails_schemaWalkInitFrame (outBase : Word) :
    WP.Entails (schemaWalkInitFrameFromPrologue outBase) (schemaWalkInitFrame outBase) := by
  intro h hp
  unfold schemaWalkInitFrameFromPrologue at hp
  unfold schemaWalkInitFrame
  exact sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x12 outBase)) h hp

/-- Callee-save and stack resources produced by the prologue and preserved through
    the short-list success slice. -/
def walkInitShortSuccessPrologueSavedFrame
    (sp0 raVal s0Old s1Old s2Old : Word) : Assertion :=
  ((.x2 ↦ᵣ prologueFrameBase sp0) ** (.x9 ↦ᵣ s1Old) ** (.x18 ↦ᵣ s2Old) **
    (prologueFrameBase sp0 ↦ₘ raVal) **
    ((prologueFrameBase sp0 + 8) ↦ₘ s0Old) **
    ((prologueFrameBase sp0 + 16) ↦ₘ s1Old) **
    ((prologueFrameBase sp0 + 24) ↦ₘ s2Old))

theorem walkInitShortSuccessPrologueSavedFrame_pcFree
    (sp0 raVal s0Old s1Old s2Old : Word) :
    (walkInitShortSuccessPrologueSavedFrame sp0 raVal s0Old s1Old s2Old).pcFree := by
  unfold walkInitShortSuccessPrologueSavedFrame
  pcFree

/-- Resources framed across the prologue so the walk-init/schema WP slice can
    start immediately at the prologue exit. -/
def walkInitShortSuccessPrologueCarryFrame
    (inputBase listLen t0Old t1Old outBase : Word) (input : List Byte) : Assertion :=
  ((.x10 ↦ᵣ (inputBase + BitVec.ofNat 64 0)) ** (.x11 ↦ᵣ listLen) **
    (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** bytesRegion inputBase input **
    bytesRegion outBase (List.replicate outputSize (0 : Byte)))

theorem walkInitShortSuccessPrologueCarryFrame_pcFree
    (inputBase listLen t0Old t1Old outBase : Word) (input : List Byte) :
    (walkInitShortSuccessPrologueCarryFrame inputBase listLen t0Old t1Old outBase input).pcFree := by
  unfold walkInitShortSuccessPrologueCarryFrame
  pcFree

/-- Exact midpoint precondition before weakening `x12 ↦ outBase` to
    `regOwn x12`. -/
def walkInitShortSuccessResolvedPreFromPrologue
    (inputBase listLen raVal t0Old t1Old outBase : Word) (input : List Byte) : Assertion :=
  ((walkInitEmptyFailStatusPre listLen raVal (inputBase + BitVec.ofNat 64 0) **
    (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion inputBase input) **
    schemaWalkInitFrameFromPrologue outBase)

theorem walkInitShortSuccessResolvedPreFromPrologue_entails_pre
    (inputBase listLen raVal t0Old t1Old outBase : Word) (input : List Byte) :
    WP.Entails
      (walkInitShortSuccessResolvedPreFromPrologue inputBase listLen raVal t0Old t1Old
        outBase input)
      (((walkInitEmptyFailStatusPre listLen raVal (inputBase + BitVec.ofNat 64 0) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion inputBase input) **
        schemaWalkInitFrame outBase)) := by
  intro h hp
  unfold walkInitShortSuccessResolvedPreFromPrologue at hp
  exact sepConj_mono_right (schemaWalkInitFrameFromPrologue_entails_schemaWalkInitFrame outBase) h hp

/-- Resources framed across the prologue so the ABI-failure walk-init classifier
    can start directly at the prologue exit. The output buffer is arbitrary
    because failure posts only report status, not decoded output bytes. -/
def walkInitAbiFailurePrologueCarryFrame
    (inputBase listLen t0Old t1Old outBase : Word) (input : List Byte) : Assertion :=
  ((.x10 ↦ᵣ (inputBase + BitVec.ofNat 64 0)) ** (.x11 ↦ᵣ listLen) **
    (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
    bytesRegion inputBase input ** bytesRegionAny outBase outputSize)

theorem walkInitAbiFailurePrologueCarryFrame_pcFree
    (inputBase listLen t0Old t1Old outBase : Word) (input : List Byte) :
    (walkInitAbiFailurePrologueCarryFrame inputBase listLen t0Old t1Old outBase input).pcFree := by
  unfold walkInitAbiFailurePrologueCarryFrame
  pcFree

/-- Prologue-owned resources that the ABI-failure classifier does not consume. -/
def walkInitAbiFailurePrologueSavedFrame
    (sp0 raVal s0Old s1Old s2Old outBase : Word) : Assertion :=
  ((.x2 ↦ᵣ prologueFrameBase sp0) ** (.x8 ↦ᵣ outBase) ** (.x9 ↦ᵣ s1Old) **
    (.x18 ↦ᵣ s2Old) ** (.x12 ↦ᵣ outBase) **
    (prologueFrameBase sp0 ↦ₘ raVal) **
    ((prologueFrameBase sp0 + 8) ↦ₘ s0Old) **
    ((prologueFrameBase sp0 + 16) ↦ₘ s1Old) **
    ((prologueFrameBase sp0 + 24) ↦ₘ s2Old))

theorem walkInitAbiFailurePrologueSavedFrame_pcFree
    (sp0 raVal s0Old s1Old s2Old outBase : Word) :
    (walkInitAbiFailurePrologueSavedFrame sp0 raVal s0Old s1Old s2Old outBase).pcFree := by
  unfold walkInitAbiFailurePrologueSavedFrame
  pcFree

/-- Exact ABI-failure classifier precondition after the decoder prologue. -/
def walkInitAbiFailurePreFromPrologue
    (inputBase listLen raVal t0Old t1Old outBase : Word) (input : List Byte) : Assertion :=
  ((walkInitEmptyFailStatusPre listLen raVal (inputBase + BitVec.ofNat 64 0) **
    (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion inputBase input) **
    bytesRegionAny outBase outputSize)

/-- Resources framed across the prologue for the `input = []` walk-init split. -/
def walkInitEmptyInputPrologueCarryFrame (inputBase outBase : Word) : Assertion :=
  ((.x10 ↦ᵣ (inputBase + BitVec.ofNat 64 0)) ** (.x11 ↦ᵣ (0 : Word)) **
    (.x0 ↦ᵣ (0 : Word)) ** emptyInputAbiFrame inputBase outBase)

theorem walkInitEmptyInputPrologueCarryFrame_pcFree (inputBase outBase : Word) :
    (walkInitEmptyInputPrologueCarryFrame inputBase outBase).pcFree := by
  unfold walkInitEmptyInputPrologueCarryFrame
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (emptyInputAbiFrame_pcFree inputBase outBase)))

/-- Exact empty-input walk-init precondition after the decoder prologue. -/
def walkInitEmptyInputPreFromPrologue
    (inputBase outBase raVal : Word) : Assertion :=
  walkInitEmptyFailStatusPre (0 : Word) raVal (inputBase + BitVec.ofNat 64 0) **
    emptyInputAbiFrame inputBase outBase

/-- Scratch registers carried across the empty-input path to match the nonempty
    classifier's static caller frame. -/
def walkInitEmptyInputPrologueScratchFrame (t0Old t1Old : Word) : Assertion :=
  ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old))

theorem walkInitEmptyInputPrologueScratchFrame_pcFree (t0Old t1Old : Word) :
    (walkInitEmptyInputPrologueScratchFrame t0Old t1Old).pcFree := by
  unfold walkInitEmptyInputPrologueScratchFrame
  pcFree

-- WP-link automation unfolds these small assertion-shape helpers before `xperm`.
attribute [rv64_wp] schemaWalkInitFrameFromPrologue walkInitShortSuccessPrologueSavedFrame
  walkInitShortSuccessPrologueCarryFrame walkInitShortSuccessResolvedPreFromPrologue
  walkInitAbiFailurePrologueCarryFrame walkInitAbiFailurePrologueSavedFrame
  walkInitAbiFailurePreFromPrologue walkInitEmptyInputPrologueCarryFrame
  walkInitEmptyInputPreFromPrologue walkInitEmptyInputPrologueScratchFrame emptyInputAbiFrame
  walkInitEmptyNotListAbiFailureNBranch_pre walkInitEmptyInputFailureNBranch_pre
  walkInitEmptyFailNotListFailShortLongOutputNBranch_pre walkInitEmptyFailStatusPre
  walkInitZeroNonzeroPre failStatusReturnPre statusReturnPre

/-- Link the concrete prologue post plus failure-classifier resources to the
    exact walk-init ABI-failure precondition, preserving prologue-owned state. -/
theorem prologuePostAbiFailureCarry_entails_preFromPrologue
    (sp0 raVal s0Old s1Old s2Old inputBase listLen t0Old t1Old outBase : Word)
    (input : List Byte) :
    WP.Entails
      (prologuePost sp0 raVal s0Old s1Old s2Old outBase **
        walkInitAbiFailurePrologueCarryFrame inputBase listLen t0Old t1Old outBase input)
      (walkInitAbiFailurePreFromPrologue inputBase listLen raVal t0Old t1Old outBase input **
        walkInitAbiFailurePrologueSavedFrame sp0 raVal s0Old s1Old s2Old outBase) := by
  wp_rv64_link

/-- Link the concrete prologue post plus `input = []` resources to the exact
    empty-input walk-init precondition, preserving prologue-owned state. -/
theorem prologuePostEmptyInputCarry_entails_preFromPrologue
    (sp0 raVal s0Old s1Old s2Old inputBase outBase : Word) :
    WP.Entails
      (prologuePost sp0 raVal s0Old s1Old s2Old outBase **
        walkInitEmptyInputPrologueCarryFrame inputBase outBase)
      (walkInitEmptyInputPreFromPrologue inputBase outBase raVal **
        walkInitAbiFailurePrologueSavedFrame sp0 raVal s0Old s1Old s2Old outBase) := by
  wp_rv64_link

/-- The empty-input caller frame is the ABI-failure caller frame specialized to
    zero length and empty bytes, with `x5`/`x6` preserved as scratch frame. -/
theorem prologuePreAbiFailureEmptyCarry_entails_emptyScratchPre
    (sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase t0Old t1Old : Word) :
    WP.Entails
      (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
        walkInitAbiFailurePrologueCarryFrame inputBase (0 : Word) t0Old t1Old outBase
          ([] : List Byte))
      ((prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
        walkInitEmptyInputPrologueCarryFrame inputBase outBase) **
        walkInitEmptyInputPrologueScratchFrame t0Old t1Old) := by
  wp_rv64_link

/-- Link the concrete prologue post plus caller-framed walk-init resources to
    the exact resolved WP precondition, carrying the saved frame as a tail frame. -/
theorem prologuePostShortSuccessCarry_entails_resolvedPreFromPrologue
    (sp0 raVal s0Old s1Old s2Old inputBase listLen t0Old t1Old outBase : Word)
    (input : List Byte) :
    WP.Entails
      (prologuePost sp0 raVal s0Old s1Old s2Old outBase **
        walkInitShortSuccessPrologueCarryFrame inputBase listLen t0Old t1Old outBase input)
      (walkInitShortSuccessResolvedPreFromPrologue inputBase listLen raVal t0Old t1Old outBase
        input ** walkInitShortSuccessPrologueSavedFrame sp0 raVal s0Old s1Old s2Old) := by
  wp_rv64_link

/-- Public handoff link from the prologue post to the reduced resolved WP
    precondition, with the prologue saved frame preserved for later epilogue work. -/
theorem prologuePostShortSuccessCarry_entails_resolvedPre
    (sp0 raVal s0Old s1Old s2Old inputBase listLen t0Old t1Old outBase : Word)
    (input : List Byte) :
    WP.Entails
      (prologuePost sp0 raVal s0Old s1Old s2Old outBase **
        walkInitShortSuccessPrologueCarryFrame inputBase listLen t0Old t1Old outBase input)
      ((((walkInitEmptyFailStatusPre listLen raVal (inputBase + BitVec.ofNat 64 0) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion inputBase input) **
        schemaWalkInitFrame outBase) **
        walkInitShortSuccessPrologueSavedFrame sp0 raVal s0Old s1Old s2Old)) := by
  intro h hp
  have hpExact := prologuePostShortSuccessCarry_entails_resolvedPreFromPrologue
    sp0 raVal s0Old s1Old s2Old inputBase listLen t0Old t1Old outBase input h hp
  exact sepConj_mono_left
    (walkInitShortSuccessResolvedPreFromPrologue_entails_pre inputBase listLen raVal t0Old
      t1Old outBase input) h hpExact

def walkInitEmptyFailSchemaAbiFrame (listLen t0Old t1Old outBase : Word) : Assertion :=
  walkInitEmptyFailAbiFrame listLen t0Old t1Old ** schemaWalkInitRegsFrame outBase

def walkInitNotListFailSchemaAbiFrame
    (inputBase listLen outBase : Word) (input : List Byte)
    (hoff : 0 < input.length) : Assertion :=
  walkInitNotListFailAbiFrame inputBase listLen input 0 hoff ** schemaWalkInitRegsFrame outBase

/-- Empty-input branch, with the schema handoff frame weakened to the public ABI
    failure post plus preserved scratch facts. -/
theorem walkInitEmptyFailSchemaPost_entails_abiFailureFrame
    (inputBase listLen raVal t0Old t1Old outBase : Word) (input : List Byte)
    (hLen : listLen = BitVec.ofNat 64 input.length)
    (hBound : input.length < 2 ^ 64) :
    WP.Entails
      ((walkInitEmptyFailStatusPost listLen raVal **
        ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion inputBase input)) **
        schemaWalkInitFrame outBase)
      (abiPost inputBase outBase raVal input **
        walkInitEmptyFailSchemaAbiFrame listLen t0Old t1Old outBase) := by
  intro h hp
  have hpCase := hp
  unfold walkInitEmptyFailStatusPost failStatusReturnPost statusReturnPost walkInitZeroPost at hpCase
  rcases hpCase with ⟨hA, _hSchema, _hdSchema, _hunionSchema, hA_prop, _hSchema_prop⟩
  rcases hA_prop with ⟨hB, _hInputRegs, _hdInputRegs, _hunionInputRegs, hB_prop, _hInputRegs_prop⟩
  rcases hB_prop with ⟨_hRegs, _hPureFrame, _hdPureFrame, _hunionPureFrame,
    _hRegs_prop, hPureFrame_prop⟩
  have hPureCopy := hPureFrame_prop
  extract_pure hPureCopy
  have hzero : listLen = (0 : Word) := hPureCopy.1
  have hLengthZero : input.length = 0 := by
    have heq : BitVec.ofNat 64 input.length = (0 : Word) := by
      rw [← hLen]
      exact hzero
    have htn := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from by decide] at htn
    rw [Nat.mod_eq_of_lt hBound] at htn
    exact htn
  have hnil : input = [] := by
    cases input with
    | nil => rfl
    | cons _ _ => simp at hLengthZero
  have hdec : decodeWithdrawal input = none := by
    rw [hnil]
    exact decodeWithdrawal_nil
  have hpAny :
      ((walkInitEmptyFailStatusPost listLen raVal **
        ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion inputBase input)) **
        schemaWalkInitAnyFrame outBase) h := by
    exact sepConj_mono_right (schemaWalkInitFrame_entails_anyFrame outBase) h hp
  unfold walkInitEmptyFailStatusPost failStatusReturnPost statusReturnPost walkInitZeroPost at hpAny
  unfold schemaWalkInitAnyFrame at hpAny
  unfold abiPost walkInitEmptyFailSchemaAbiFrame walkInitEmptyFailAbiFrame schemaWalkInitRegsFrame
  rw [resultPost_failure hdec]
  rw [show (⌜decodeWithdrawal input = none⌝ : Assertion) = empAssertion by
    funext h
    unfold EvmAsm.Rv64.pure EvmAsm.Rv64.empAssertion
    apply propext
    constructor
    · intro h_p
      exact h_p.1
    · intro h_empty
      exact ⟨h_empty, hdec⟩]
  simp only [sepConj_emp_right']
  xperm_hyp hpAny

/-- Not-list branch, with the schema handoff frame weakened to the public ABI
    failure post plus preserved scratch facts. -/
theorem walkInitNotListFailSchemaPost_entails_abiFailureFrame
    (inputBase listLen raVal outBase : Word) (input : List Byte)
    (hoff : 0 < input.length) :
    WP.Entails
      (walkInitPrefixNotListFailStatusPost inputBase listLen raVal input 0 hoff **
        schemaWalkInitFrame outBase)
      (abiPost inputBase outBase raVal input **
        walkInitNotListFailSchemaAbiFrame inputBase listLen outBase input hoff) := by
  intro h hp
  have hpCase := hp
  unfold walkInitPrefixNotListFailStatusPost walkInitPrefixNotListFailStatusFrame
    walkInitPrefixWord at hpCase
  rcases hpCase with ⟨hMain, _hSchema, _hdSchema, _hunionSchema, hMain_prop, _hSchema_prop⟩
  rcases hMain_prop with ⟨_hFail, _hFrame, _hdFrame, _hunionFrame,
    _hFail_prop, hFrame_prop⟩
  rcases hFrame_prop with ⟨_hFrameHead, _hFrameTail, _hdFrameTail, _hunionFrameTail,
    _hFrameHead_prop, hFrameTail_prop⟩
  have hFrameTailPure := hFrameTail_prop
  extract_pure hFrameTailPure
  have hlt : BitVec.ult (walkInitPrefixWord input 0 hoff) (0xc0 : Word) = true :=
    hFrameTailPure.1
  have hdec : decodeWithdrawal input = none := by
    cases input with
    | nil => simp at hoff
    | cons pfx rest =>
        simpa using decodeWithdrawal_none_of_head_lt_c0 pfx rest hlt
  have hpAny :
      (walkInitPrefixNotListFailStatusPost inputBase listLen raVal input 0 hoff **
        schemaWalkInitAnyFrame outBase) h := by
    exact sepConj_mono_right (schemaWalkInitFrame_entails_anyFrame outBase) h hp
  unfold walkInitPrefixNotListFailStatusPost walkInitPrefixNotListFailStatusFrame
    failStatusReturnPost statusReturnPost walkInitPrefixWord at hpAny
  unfold schemaWalkInitAnyFrame at hpAny
  unfold abiPost walkInitNotListFailSchemaAbiFrame walkInitNotListFailAbiFrame
    schemaWalkInitRegsFrame walkInitPrefixWord
  rw [resultPost_failure hdec]
  rw [show (⌜decodeWithdrawal input = none⌝ : Assertion) = empAssertion by
    funext h
    unfold EvmAsm.Rv64.pure EvmAsm.Rv64.empAssertion
    apply propext
    constructor
    · intro h_p
      exact h_p.1
    · intro h_empty
      exact ⟨h_empty, hdec⟩]
  simp only [sepConj_emp_right']
  xperm_hyp hpAny

def walkInitShortSuccessAbiPost
    (inputBase outBase raVal : Word) (input d0 d1 d2 d3 : List Byte) : Assertion :=
  ((abiPost inputBase outBase raVal input **
    successSchemaReturnFrame inputBase outBase
      (1 + schemaEnc (successFieldSpecs d0 d1 d2 d3))) **
    (.x6 ↦ᵣ (0xf8 : Word)))

def walkInitLongSchemaPost
    (inputBase listLen raVal outBase : Word) (input : List Byte)
    (hoff : 0 < input.length) : Assertion :=
  walkInitLongListCandidatePost inputBase listLen raVal input 0 hoff ** schemaWalkInitFrame outBase

theorem walkInitPrefixWord_lt_f8_of_successFieldSpecs_input
    (input d0 d1 d2 d3 : List Byte) (hoff : 0 < input.length)
    (hl0 : d0.length ≤ 8) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20) (hl3 : d3.length ≤ 8)
    (hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3)))) :
    BitVec.ult (walkInitPrefixWord input 0 hoff) (0xf8 : Word) = true := by
  have hpayload := schemaEncBytes_successFieldSpecs_length_le_48 d0 d1 d2 d3 hl0 hl1 haddr hl3
  have hshort : (schemaEncBytes (successFieldSpecs d0 d1 d2 d3)).length ≤ 55 := by
    omega
  subst input
  simp [walkInitPrefixWord, encode_list_schemaItems_short, hshort, BitVec.ult]
  omega

theorem walkInitPrefixWord_not_lt_c0_of_successFieldSpecs_input
    (input d0 d1 d2 d3 : List Byte) (hoff : 0 < input.length)
    (hl0 : d0.length ≤ 8) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20) (hl3 : d3.length ≤ 8)
    (hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3)))) :
    BitVec.ult (walkInitPrefixWord input 0 hoff) (0xc0 : Word) = false := by
  have hpayload := schemaEncBytes_successFieldSpecs_length_le_48 d0 d1 d2 d3 hl0 hl1 haddr hl3
  have hshort : (schemaEncBytes (successFieldSpecs d0 d1 d2 d3)).length ≤ 55 := by
    omega
  subst input
  simp [walkInitPrefixWord, encode_list_schemaItems_short, hshort, BitVec.ult]
  omega

/-- The empty-input semantic failure exit is unreachable for a nonempty short-list
    success witness whose length was loaded into `listLen`. -/
theorem walkInitEmptyFailSchemaAbiPost_contradicts_successFieldSpecs_input
    (inputBase listLen raVal t0Old t1Old outBase : Word) (input : List Byte)
    (hoff : 0 < input.length) (hLen : listLen = BitVec.ofNat 64 input.length)
    (hBound : input.length < 2 ^ 64) :
    ∀ h,
      (abiPost inputBase outBase raVal input **
        walkInitEmptyFailSchemaAbiFrame listLen t0Old t1Old outBase) h → False := by
  intro h hp
  unfold walkInitEmptyFailSchemaAbiFrame walkInitEmptyFailAbiFrame at hp
  rcases hp with ⟨_hAbi, hFrame, _hdFrame, _hunionFrame, _hAbi_prop, hFrame_prop⟩
  rcases hFrame_prop with ⟨hEmpty, _hSchema, _hdSchema, _hunionSchema,
    hEmpty_prop, _hSchema_prop⟩
  rcases hEmpty_prop with ⟨_hLenReg, hRest1, _hdRest1, _hunionRest1,
    _hLenReg_prop, hRest1_prop⟩
  rcases hRest1_prop with ⟨_hX5, hRest2, _hdRest2, _hunionRest2,
    _hX5_prop, hRest2_prop⟩
  rcases hRest2_prop with ⟨_hX6, hPure, _hdPure, _hunionPure,
    _hX6_prop, hPure_prop⟩
  have hzero : listLen = (0 : Word) := hPure_prop.2
  have hLengthZero : input.length = 0 := by
    have heq : BitVec.ofNat 64 input.length = (0 : Word) := by
      rw [← hLen]
      exact hzero
    have htn := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from by decide] at htn
    rw [Nat.mod_eq_of_lt hBound] at htn
    exact htn
  omega

/-- The not-list semantic failure exit is unreachable for a short-list success
    witness, because its first byte is a list prefix. -/
theorem walkInitNotListFailSchemaAbiPost_contradicts_successFieldSpecs_input
    (inputBase listLen raVal outBase : Word) (input d0 d1 d2 d3 : List Byte)
    (hoff : 0 < input.length)
    (hl0 : d0.length ≤ 8) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20) (hl3 : d3.length ≤ 8)
    (hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3)))) :
    ∀ h,
      (abiPost inputBase outBase raVal input **
        walkInitNotListFailSchemaAbiFrame inputBase listLen outBase input hoff) h → False := by
  intro h hp
  have hnlt := walkInitPrefixWord_not_lt_c0_of_successFieldSpecs_input input d0 d1 d2 d3 hoff
    hl0 hl1 haddr hl3 hinput
  unfold walkInitNotListFailSchemaAbiFrame walkInitNotListFailAbiFrame at hp
  rcases hp with ⟨_hAbi, hFrame, _hdFrame, _hunionFrame, _hAbi_prop, hFrame_prop⟩
  rcases hFrame_prop with ⟨hNotList, _hSchema, _hdSchema, _hunionSchema,
    hNotList_prop, _hSchema_prop⟩
  rcases hNotList_prop with ⟨_hX11, hRest1, _hdRest1, _hunionRest1,
    _hX11_prop, hRest1_prop⟩
  rcases hRest1_prop with ⟨_hX5, hRest2, _hdRest2, _hunionRest2,
    _hX5_prop, hRest2_prop⟩
  rcases hRest2_prop with ⟨_hX6, hRest3, _hdRest3, _hunionRest3,
    _hX6_prop, hRest3_prop⟩
  rcases hRest3_prop with ⟨_hNonzero, hLt, _hdLt, _hunionLt,
    _hNonzero_prop, hLt_prop⟩
  have hlt : BitVec.ult (walkInitPrefixWord input 0 hoff) (0xc0 : Word) = true := hLt_prop.2
  rw [hnlt] at hlt
  contradiction

/-- The long-list exit is unreachable when the input is the short-list encoding
    of successful withdrawal field witnesses. -/
theorem walkInitLongSchemaPost_contradicts_successFieldSpecs_input
    (inputBase listLen raVal outBase : Word) (input d0 d1 d2 d3 : List Byte)
    (hoff : 0 < input.length)
    (hl0 : d0.length ≤ 8) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20) (hl3 : d3.length ≤ 8)
    (hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3)))) :
    ∀ h, walkInitLongSchemaPost inputBase listLen raVal outBase input hoff h → False := by
  intro h hp
  have hlt := walkInitPrefixWord_lt_f8_of_successFieldSpecs_input input d0 d1 d2 d3 hoff
    hl0 hl1 haddr hl3 hinput
  unfold walkInitLongSchemaPost walkInitLongListCandidatePost at hp
  rcases hp with ⟨hLong, _hSchema, _hd, _hunion, hLong_prop, _hSchema_prop⟩
  rcases hLong_prop with ⟨_hPrefix, _hPure, _hdPure, _hunionPure,
    _hPrefix_prop, hPure_prop⟩
  exact hPure_prop.2 hlt

/-- WP continuation for the dead long-list exit under a short-list success witness.
    The target and code requirement are parameters so generated joins can reuse
    the certificate in whatever larger CFG they are constructing. -/
def walkInitLongSchemaUnreachableCert
    (entry target : Word) (cr : CodeReq)
    (inputBase listLen raVal outBase : Word) (input d0 d1 d2 d3 : List Byte)
    (hoff : 0 < input.length)
    (hl0 : d0.length ≤ 8) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20) (hl3 : d3.length ≤ 8)
    (hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (post : Assertion) :
    WP.CFG.Cert entry target cr post :=
  WP.CFG.unreachable entry target cr
    (walkInitLongSchemaPost_contradicts_successFieldSpecs_input inputBase listLen raVal outBase
      input d0 d1 d2 d3 hoff hl0 hl1 haddr hl3 hinput)

theorem walkInitLongSchemaUnreachableCert_pre
    (entry target : Word) (cr : CodeReq)
    (inputBase listLen raVal outBase : Word) (input d0 d1 d2 d3 : List Byte)
    (hoff : 0 < input.length)
    (hl0 : d0.length ≤ 8) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20) (hl3 : d3.length ≤ 8)
    (hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (post : Assertion) :
    (walkInitLongSchemaUnreachableCert entry target cr inputBase listLen raVal outBase input
      d0 d1 d2 d3 hoff hl0 hl1 haddr hl3 hinput post).pre =
      walkInitLongSchemaPost inputBase listLen raVal outBase input hoff := by
  rfl

def walkInitShortSuccessSchemaExits
    (base inputBase listLen raVal t0Old t1Old outBase : Word)
    (input d0 d1 d2 d3 : List Byte) (hoff : 0 < input.length) :
    List (Word × Assertion) :=
  [ (failStatusReturnExit raVal,
      (walkInitEmptyFailStatusPost listLen raVal **
        ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion inputBase input)) **
        schemaWalkInitFrame outBase)
  , (failStatusReturnExit raVal,
      walkInitPrefixNotListFailStatusPost inputBase listLen raVal input 0 hoff **
        schemaWalkInitFrame outBase)
  , (successStatusReturnExit raVal,
      walkInitShortSuccessAbiPost inputBase outBase raVal input d0 d1 d2 d3)
  , (base + 28,
      walkInitLongSchemaPost inputBase listLen raVal outBase input hoff)
  ]

theorem walkInitShortSuccessSchemaNBranch_exits
    (base inputBase listLen raVal t0Old t1Old outBase : Word)
    (input d0 d1 d2 d3 : List Byte)
    (hsalign : inputBase.toNat % 8 = 0) (hoff : 0 < input.length)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : ∀ i, i < input.length → isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (hcode : base.toNat + 172 + 4 + schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    (walkInitShortSuccessSchemaNBranch base inputBase listLen raVal t0Old t1Old outBase input
      d0 d1 d2 d3 hsalign hoff hover hwin hdalign hdov hdval hc0 hl0 hc1 hl1 haddr hc3
      hl3 hinput hcode).exits =
      walkInitShortSuccessSchemaExits base inputBase listLen raVal t0Old t1Old outBase input
        d0 d1 d2 d3 hoff := by
  unfold walkInitShortSuccessSchemaNBranch walkInitShortSuccessSchemaExits
    walkInitShortSuccessAbiPost walkInitLongSchemaPost
  rfl

def walkInitShortSuccessSemanticExits
    (base inputBase listLen raVal t0Old t1Old outBase : Word)
    (input d0 d1 d2 d3 : List Byte) (hoff : 0 < input.length) :
    List (Word × Assertion) :=
  [ (failStatusReturnExit raVal,
      abiPost inputBase outBase raVal input **
        walkInitEmptyFailSchemaAbiFrame listLen t0Old t1Old outBase)
  , (failStatusReturnExit raVal,
      abiPost inputBase outBase raVal input **
        walkInitNotListFailSchemaAbiFrame inputBase listLen outBase input hoff)
  , (successStatusReturnExit raVal,
      walkInitShortSuccessAbiPost inputBase outBase raVal input d0 d1 d2 d3)
  , (base + 28,
      walkInitLongSchemaPost inputBase listLen raVal outBase input hoff)
  ]

/-- Prefix classifier with semantic failure exits and the short-list success path
    continued through the generated result-free schema WP tail. The long-list
    exit remains open. -/
def walkInitShortSuccessSemanticNBranch
    (base inputBase listLen raVal t0Old t1Old outBase : Word)
    (input d0 d1 d2 d3 : List Byte)
    (hsalign : inputBase.toNat % 8 = 0) (hoff : 0 < input.length)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : ∀ i, i < input.length → isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (hLen : listLen = BitVec.ofNat 64 input.length)
    (hcode : base.toNat + 172 + 4 + schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    WP.NBranch base
      ((walkInitEmptyFailNotListFailShortLongCode base).union
        ((walkInitShortSuccessJumpCode base).union
          ((schemaCursorInitCode (base + 172)).union
            ((schemaCR (base + 172 + 4) .x8 (successFieldSpecs d0 d1 d2 d3)).union
              (successStatusReturnCode
                ((base + 172 + 4) + BitVec.ofNat 64
                  (schemaSize (successFieldSpecs d0 d1 d2 d3)))))))) := by
  let br := walkInitShortSuccessSchemaNBranch base inputBase listLen raVal t0Old t1Old outBase
    input d0 d1 d2 d3 hsalign hoff hover hwin hdalign hdov hdval hc0 hl0 hc1 hl1 haddr
    hc3 hl3 hinput hcode
  have hBound : input.length < 2 ^ 64 := by
    omega
  wp_rv64_nbranch_weaken_posts4_with br,
    (walkInitShortSuccessSchemaNBranch_exits base inputBase listLen raVal t0Old t1Old
      outBase input d0 d1 d2 d3 hsalign hoff hover hwin hdalign hdov hdval hc0 hl0 hc1 hl1
      haddr hc3 hl3 hinput hcode),
    (walkInitEmptyFailSchemaPost_entails_abiFailureFrame inputBase listLen raVal t0Old
      t1Old outBase input hLen hBound),
    (walkInitNotListFailSchemaPost_entails_abiFailureFrame inputBase listLen raVal outBase
      input hoff),
    (WP.Entails.refl _),
    (WP.Entails.refl _)

theorem walkInitShortSuccessSemanticNBranch_pre
    (base inputBase listLen raVal t0Old t1Old outBase : Word)
    (input d0 d1 d2 d3 : List Byte)
    (hsalign : inputBase.toNat % 8 = 0) (hoff : 0 < input.length)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : ∀ i, i < input.length → isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (hLen : listLen = BitVec.ofNat 64 input.length)
    (hcode : base.toNat + 172 + 4 + schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    (walkInitShortSuccessSemanticNBranch base inputBase listLen raVal t0Old t1Old outBase input
      d0 d1 d2 d3 hsalign hoff hover hwin hdalign hdov hdval hc0 hl0 hc1 hl1 haddr hc3
      hl3 hinput hLen hcode).pre =
      (walkInitShortSuccessSchemaNBranch base inputBase listLen raVal t0Old t1Old outBase input
        d0 d1 d2 d3 hsalign hoff hover hwin hdalign hdov hdval hc0 hl0 hc1 hl1 haddr hc3
        hl3 hinput hcode).pre := by
  rfl

theorem walkInitShortSuccessSemanticNBranch_exits
    (base inputBase listLen raVal t0Old t1Old outBase : Word)
    (input d0 d1 d2 d3 : List Byte)
    (hsalign : inputBase.toNat % 8 = 0) (hoff : 0 < input.length)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : ∀ i, i < input.length → isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (hLen : listLen = BitVec.ofNat 64 input.length)
    (hcode : base.toNat + 172 + 4 + schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    (walkInitShortSuccessSemanticNBranch base inputBase listLen raVal t0Old t1Old outBase input
      d0 d1 d2 d3 hsalign hoff hover hwin hdalign hdov hdval hc0 hl0 hc1 hl1 haddr hc3
      hl3 hinput hLen hcode).exits =
      walkInitShortSuccessSemanticExits base inputBase listLen raVal t0Old t1Old outBase input
        d0 d1 d2 d3 hoff := by
  rfl

/-- The short-success semantic classifier joined to a single success post.  The
    empty, not-list, and long-list exits are closed by contradiction from the
    success witness; the only reachable exit is the schema success post. -/
def walkInitShortSuccessResolvedCert
    (base inputBase listLen raVal t0Old t1Old outBase : Word)
    (input d0 d1 d2 d3 : List Byte)
    (hsalign : inputBase.toNat % 8 = 0) (hoff : 0 < input.length)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : ∀ i, i < input.length → isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (hLen : listLen = BitVec.ofNat 64 input.length)
    (hcode : base.toNat + 172 + 4 + schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    WP.CFG.Cert base (successStatusReturnExit raVal)
      ((walkInitEmptyFailNotListFailShortLongCode base).union
        ((walkInitShortSuccessJumpCode base).union
          ((schemaCursorInitCode (base + 172)).union
            ((schemaCR (base + 172 + 4) .x8 (successFieldSpecs d0 d1 d2 d3)).union
              (successStatusReturnCode
                ((base + 172 + 4) + BitVec.ofNat 64
                  (schemaSize (successFieldSpecs d0 d1 d2 d3))))))))
      (walkInitShortSuccessAbiPost inputBase outBase raVal input d0 d1 d2 d3) := by
  let cr := ((walkInitEmptyFailNotListFailShortLongCode base).union
    ((walkInitShortSuccessJumpCode base).union
      ((schemaCursorInitCode (base + 172)).union
        ((schemaCR (base + 172 + 4) .x8 (successFieldSpecs d0 d1 d2 d3)).union
          (successStatusReturnCode
            ((base + 172 + 4) + BitVec.ofNat 64
              (schemaSize (successFieldSpecs d0 d1 d2 d3))))))))
  let br := walkInitShortSuccessSemanticNBranch base inputBase listLen raVal t0Old t1Old outBase
    input d0 d1 d2 d3 hsalign hoff hover hwin hdalign hdov hdval hc0 hl0 hc1 hl1 haddr
    hc3 hl3 hinput hLen hcode
  have hexits : br.exits =
      walkInitShortSuccessSemanticExits base inputBase listLen raVal t0Old t1Old outBase input
        d0 d1 d2 d3 hoff := by
    dsimp [br]
    rw [walkInitShortSuccessSemanticNBranch_exits]
  have hBound : input.length < 2 ^ 64 := by
    omega
  have hexits4 : br.exits =
      [(failStatusReturnExit raVal,
          abiPost inputBase outBase raVal input **
            walkInitEmptyFailSchemaAbiFrame listLen t0Old t1Old outBase),
        (failStatusReturnExit raVal,
          abiPost inputBase outBase raVal input **
            walkInitNotListFailSchemaAbiFrame inputBase listLen outBase input hoff),
        (successStatusReturnExit raVal,
          walkInitShortSuccessAbiPost inputBase outBase raVal input d0 d1 d2 d3),
        (base + 28,
          walkInitLongSchemaPost inputBase listLen raVal outBase input hoff)] := by
    simpa [walkInitShortSuccessSemanticExits] using hexits
  wp_rv64_nbranch_join4_resolve_third br, hexits4,
    (walkInitEmptyFailSchemaAbiPost_contradicts_successFieldSpecs_input inputBase listLen
      raVal t0Old t1Old outBase input hoff hLen hBound),
    (walkInitNotListFailSchemaAbiPost_contradicts_successFieldSpecs_input inputBase
      listLen raVal outBase input d0 d1 d2 d3 hoff hl0 hl1 haddr hl3 hinput),
    (WP.Entails.refl _),
    (walkInitLongSchemaPost_contradicts_successFieldSpecs_input inputBase listLen raVal
      outBase input d0 d1 d2 d3 hoff hl0 hl1 haddr hl3 hinput)

theorem walkInitShortSuccessResolvedCert_pre
    (base inputBase listLen raVal t0Old t1Old outBase : Word)
    (input d0 d1 d2 d3 : List Byte)
    (hsalign : inputBase.toNat % 8 = 0) (hoff : 0 < input.length)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : ∀ i, i < input.length → isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (hLen : listLen = BitVec.ofNat 64 input.length)
    (hcode : base.toNat + 172 + 4 + schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    (walkInitShortSuccessResolvedCert base inputBase listLen raVal t0Old t1Old outBase input
      d0 d1 d2 d3 hsalign hoff hover hwin hdalign hdov hdval hc0 hl0 hc1 hl1 haddr hc3
      hl3 hinput hLen hcode).pre =
      (walkInitShortSuccessSemanticNBranch base inputBase listLen raVal t0Old t1Old outBase input
        d0 d1 d2 d3 hsalign hoff hover hwin hdalign hdov hdval hc0 hl0 hc1 hl1 haddr hc3
        hl3 hinput hLen hcode).pre := by
  unfold walkInitShortSuccessResolvedCert
  rfl


/-- Fully reduced WP precondition for the short-list success classifier.  The
    precondition is still result-free: it contains the input bytes, the loaded
    length, scratch registers, and the zeroed schema handoff frame, but no
    decoded withdrawal value. -/
theorem walkInitShortSuccessResolvedCert_pre_expanded
    (base inputBase listLen raVal t0Old t1Old outBase : Word)
    (input d0 d1 d2 d3 : List Byte)
    (hsalign : inputBase.toNat % 8 = 0) (hoff : 0 < input.length)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : ∀ i, i < input.length → isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (hLen : listLen = BitVec.ofNat 64 input.length)
    (hcode : base.toNat + 172 + 4 + schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    (walkInitShortSuccessResolvedCert base inputBase listLen raVal t0Old t1Old outBase input
      d0 d1 d2 d3 hsalign hoff hover hwin hdalign hdov hdval hc0 hl0 hc1 hl1 haddr hc3
      hl3 hinput hLen hcode).pre =
      ((walkInitEmptyFailStatusPre listLen raVal (inputBase + BitVec.ofNat 64 0) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion inputBase input) **
        schemaWalkInitFrame outBase) := by
  rw [walkInitShortSuccessResolvedCert_pre,
    walkInitShortSuccessSemanticNBranch_pre,
    walkInitShortSuccessSchemaNBranch_pre]

/-- Traditional CPS statement for the resolved short-list success slice, using
    the fully reduced WP precondition. -/
theorem walkInitShortSuccessResolved_spec_within
    (base inputBase listLen raVal t0Old t1Old outBase : Word)
    (input d0 d1 d2 d3 : List Byte)
    (hsalign : inputBase.toNat % 8 = 0) (hoff : 0 < input.length)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : ∀ i, i < input.length → isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (hLen : listLen = BitVec.ofNat 64 input.length)
    (hcode : base.toNat + 172 + 4 + schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    cpsTripleWithin
      (walkInitShortSuccessResolvedCert base inputBase listLen raVal t0Old t1Old outBase input
        d0 d1 d2 d3 hsalign hoff hover hwin hdalign hdov hdval hc0 hl0 hc1 hl1 haddr hc3
        hl3 hinput hLen hcode).nSteps
      base (successStatusReturnExit raVal)
      ((walkInitEmptyFailNotListFailShortLongCode base).union
        ((walkInitShortSuccessJumpCode base).union
          ((schemaCursorInitCode (base + 172)).union
            ((schemaCR (base + 172 + 4) .x8 (successFieldSpecs d0 d1 d2 d3)).union
              (successStatusReturnCode
                ((base + 172 + 4) + BitVec.ofNat 64
                  (schemaSize (successFieldSpecs d0 d1 d2 d3))))))))
      (((walkInitEmptyFailStatusPre listLen raVal (inputBase + BitVec.ofNat 64 0) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** bytesRegion inputBase input) **
        schemaWalkInitFrame outBase))
      (walkInitShortSuccessAbiPost inputBase outBase raVal input d0 d1 d2 d3) := by
  rw [← walkInitShortSuccessResolvedCert_pre_expanded]
  exact (walkInitShortSuccessResolvedCert base inputBase listLen raVal t0Old t1Old outBase input
    d0 d1 d2 d3 hsalign hoff hover hwin hdalign hdov hdval hc0 hl0 hc1 hl1 haddr hc3
    hl3 hinput hLen hcode).sound


/-- Code covered by the resolved short-list success WP slice.  This aliases the
    generated union so higher-level WP composition can name the tail as a unit. -/
def walkInitShortSuccessResolvedCode (base : Word) (specs : List FieldSpec) : CodeReq :=
  ((walkInitEmptyFailNotListFailShortLongCode base).union
    ((walkInitShortSuccessJumpCode base).union
      ((schemaCursorInitCode (base + 172)).union
        ((schemaCR (base + 172 + 4) .x8 specs).union
          (successStatusReturnCode
            ((base + 172 + 4) + BitVec.ofNat 64 (schemaSize specs)))))))


attribute [rv64_wp] walkInitShortSuccessResolvedCode

/-- The decoder prologue occupies exactly the first six 4-byte instructions. -/
theorem prologueCode_none_above (base a : Word)
    (hbound : base.toNat + 24 < 2 ^ 64) (h : base.toNat + 24 ≤ a.toNat) :
    prologueCode base a = none := by
  unfold prologueCode
  exact CodeReq.ofProg_none_range_len base prologue 6 a prologue_length (fun k hk => by
    bv_omega)

/-- The walk-init classifier prefix used by the short-success slice has no code
    below its entry address, assuming its code range does not wrap. -/
theorem walkInitEmptyFailNotListFailShortLongCode_none_below
    (base a : Word) (hcode : base.toNat + 172 < 2 ^ 64) (h : a.toNat < base.toNat) :
    walkInitEmptyFailNotListFailShortLongCode base a = none := by
  unfold walkInitEmptyFailNotListFailShortLongCode walkInitEmptyFailOrPrefixCode
    walkInitEmptyFailStatusCode failStatusReturnCode statusReturnCode
    walkInitNonzeroPrefixTailCode walkInitPrefixShortLongTailCode
    walkInitPrefixListCheckNotListFailF8Code walkInitPrefixListCheckOrNotListFailCode
    walkInitPrefixListCheckCode walkInitPrefixNotListFailStatusCode walkInitListF8Code
    walkInitShortLongCheckCode
  have h0 : CodeReq.singleton base (.BEQ .x11 .x0 (156 : BitVec 13)) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h156 : CodeReq.singleton (base + 156) (.LI .x10 (1 : Word)) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h160 : CodeReq.singleton (base + 156 + 4) (.JALR .x0 .x1 (0 : BitVec 12)) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h4 : CodeReq.singleton (base + 4) (.ADD .x11 .x10 .x11) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h8 : CodeReq.singleton (base + 8) (.LBU .x5 .x10 0) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h12 : CodeReq.singleton (base + 12) (.LI .x6 (0xc0 : Word)) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h16 : CodeReq.singleton (base + 16) (.BLTU .x5 .x6 (148 : BitVec 13)) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h164 : CodeReq.singleton (base + 164) (.LI .x10 (1 : Word)) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h168 : CodeReq.singleton (base + 164 + 4) (.JALR .x0 .x1 (0 : BitVec 12)) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h20 : CodeReq.singleton (base + 20) (.LI .x6 (0xf8 : Word)) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h24 : CodeReq.singleton (base + 24) (.BLTU .x5 .x6 (100 : BitVec 13)) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  simp only [failStatusReturnCode, statusReturnCode, CodeReq.union,
    h0, h156, h160, h4, h8, h12, h16, h164, h168, h20, h24]

/-- The resolved short-success tail has no code below its entry address. -/
theorem walkInitShortSuccessResolvedCode_none_below
    (base : Word) (specs : List FieldSpec) (a : Word)
    (hcode : base.toNat + 172 + 4 + schemaSize specs + 8 < 2 ^ 64)
    (h : a.toNat < base.toNat) :
    walkInitShortSuccessResolvedCode base specs a = none := by
  have hbase172 : (base + 172).toNat = base.toNat + 172 := by
    bv_omega
  have h0 : walkInitEmptyFailNotListFailShortLongCode base a = none :=
    walkInitEmptyFailNotListFailShortLongCode_none_below base a (by omega) h
  have h1 : walkInitShortSuccessJumpCode base a = none := by
    unfold walkInitShortSuccessJumpCode
    exact CodeReq.singleton_miss (by
      intro h_eq
      have := congrArg BitVec.toNat h_eq
      bv_omega)
  have h2 :
      ((schemaCursorInitCode (base + 172)).union
        ((schemaCR (base + 172 + 4) .x8 specs).union
          (successStatusReturnCode
            ((base + 172 + 4) + BitVec.ofNat 64 (schemaSize specs))))) a = none :=
    schemaCursorInitSuccessReturnTail_none_below (base + 172) .x8 specs a
      (by rw [hbase172]; omega) (by rw [hbase172]; omega)
  unfold walkInitShortSuccessResolvedCode
  simp only [CodeReq.union, h0, h1]
  exact h2

/-- Range split between the prologue and the resolved short-success tail. -/
theorem prologueCode_disjoint_walkInitShortSuccessResolvedCode
    (base : Word) (specs : List FieldSpec)
    (hprologue : base.toNat + 24 < 2 ^ 64)
    (htail : (base + 24).toNat + 172 + 4 + schemaSize specs + 8 < 2 ^ 64) :
    (prologueCode base).Disjoint (walkInitShortSuccessResolvedCode (base + 24) specs) := by
  have hbase24 : (base + 24).toNat = base.toNat + 24 := by
    bv_omega
  refine codeReq_disjoint_of_ranges _ _ (base.toNat + 24) ?_ ?_
  · intro a ha
    exact prologueCode_none_above base a hprologue ha
  · intro a ha
    exact walkInitShortSuccessResolvedCode_none_below (base + 24) specs a htail
      (by rw [hbase24]; exact ha)

/-- Range split between the decoder prologue and the standalone walk-init
    classifier. -/
theorem prologueCode_disjoint_walkInitEmptyFailNotListFailShortLongCode
    (base : Word)
    (hprologue : base.toNat + 24 < 2 ^ 64)
    (htail : (base + 24).toNat + 172 < 2 ^ 64) :
    (prologueCode base).Disjoint
      (walkInitEmptyFailNotListFailShortLongCode (base + 24)) := by
  have hbase24 : (base + 24).toNat = base.toNat + 24 := by
    bv_omega
  refine codeReq_disjoint_of_ranges _ _ (base.toNat + 24) ?_ ?_
  · intro a ha
    exact prologueCode_none_above base a hprologue ha
  · intro a ha
    exact walkInitEmptyFailNotListFailShortLongCode_none_below (base + 24) a htail
      (by rw [hbase24]; exact ha)

/-- The empty-input walk-init status block has no code below its entry address. -/
theorem walkInitEmptyFailStatusCode_none_below
    (base a : Word) (hcode : base.toNat + 164 < 2 ^ 64) (h : a.toNat < base.toNat) :
    walkInitEmptyFailStatusCode base a = none := by
  unfold walkInitEmptyFailStatusCode failStatusReturnCode statusReturnCode
  have h0 : CodeReq.singleton base (.BEQ .x11 .x0 (156 : BitVec 13)) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h156 : CodeReq.singleton (base + 156) (.LI .x10 (1 : Word)) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  have h160 : CodeReq.singleton (base + 156 + 4) (.JALR .x0 .x1 (0 : BitVec 12)) a = none :=
    CodeReq.singleton_miss (by bv_omega)
  simp only [CodeReq.union, h0, h156, h160]

/-- Range split between the decoder prologue and the empty-input status block. -/
theorem prologueCode_disjoint_walkInitEmptyFailStatusCode
    (base : Word)
    (hprologue : base.toNat + 24 < 2 ^ 64)
    (htail : (base + 24).toNat + 164 < 2 ^ 64) :
    (prologueCode base).Disjoint (walkInitEmptyFailStatusCode (base + 24)) := by
  have hbase24 : (base + 24).toNat = base.toNat + 24 := by
    bv_omega
  refine codeReq_disjoint_of_ranges _ _ (base.toNat + 24) ?_ ?_
  · intro a ha
    exact prologueCode_none_above base a hprologue ha
  · intro a ha
    exact walkInitEmptyFailStatusCode_none_below (base + 24) a htail
      (by rw [hbase24]; exact ha)

/-- Prologue followed by the empty-input walk-init failure split. The taken exit
    carries the semantic `decodeWithdrawal [] = none` failure fact, while the
    nonzero exit remains explicit and contradictory for `listLen = 0`. -/
def walkInitEmptyInputFailureFromPrologueNBranch
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase : Word)
    (hprologueCode : base.toNat + 24 < 2 ^ 64)
    (hcode : (base + 24).toNat + 164 < 2 ^ 64) :
    WP.NBranch base
      ((prologueCode base).union (walkInitEmptyFailStatusCode (base + 24))) := by
  let carryFrame := walkInitEmptyInputPrologueCarryFrame inputBase outBase
  let savedFrame := walkInitAbiFailurePrologueSavedFrame sp0 raVal s0Old s1Old s2Old outBase
  let head := prologueCert base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
  let tail := walkInitEmptyInputFailureNBranch (base + 24) inputBase outBase raVal
    (inputBase + BitVec.ofNat 64 0)
  have hlink : WP.Entails
      (prologuePost sp0 raVal s0Old s1Old s2Old outBase ** carryFrame)
      (tail.pre ** savedFrame) := by
    dsimp [tail, carryFrame, savedFrame]
    simp only [walkInitEmptyInputFailureNBranch_pre]
    exact prologuePostEmptyInputCarry_entails_preFromPrologue sp0 raVal s0Old s1Old s2Old
      inputBase outBase
  wp_rv64_seq_block_nbranch_framed_disjoint_with
    (prologueCode_disjoint_walkInitEmptyFailStatusCode base hprologueCode hcode),
    head, carryFrame,
    (walkInitEmptyInputPrologueCarryFrame_pcFree inputBase outBase),
    tail, savedFrame,
    (walkInitAbiFailurePrologueSavedFrame_pcFree sp0 raVal s0Old s1Old s2Old outBase),
    hlink

/-- Expanded precondition for the prologue-to-empty-input failure split. -/
theorem walkInitEmptyInputFailureFromPrologueNBranch_pre
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase : Word)
    (hprologueCode : base.toNat + 24 < 2 ^ 64)
    (hcode : (base + 24).toNat + 164 < 2 ^ 64) :
    (walkInitEmptyInputFailureFromPrologueNBranch base sp0 raVal s0Old s1Old s2Old
      outBase m0 m1 m2 m3 inputBase hprologueCode hcode).pre =
      (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
        walkInitEmptyInputPrologueCarryFrame inputBase outBase) := by
  rfl

/-- Empty-input path stated over the full walk-init classifier code. This lets
    later zero/nonzero wrappers use one code requirement for both empty and
    nonempty inputs. -/
def walkInitEmptyInputFailureFromPrologueFullCodeNBranch
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase : Word)
    (hprologueCode : base.toNat + 24 < 2 ^ 64)
    (hcode : (base + 24).toNat + 172 < 2 ^ 64) :
    WP.NBranch base
      ((prologueCode base).union
        (walkInitEmptyFailNotListFailShortLongCode (base + 24))) := by
  let br := walkInitEmptyInputFailureFromPrologueNBranch base sp0 raVal s0Old s1Old s2Old
    outBase m0 m1 m2 m3 inputBase hprologueCode (by omega)
  wp_rv64_nbranch_extend_code br, (by
    intro a i h
    cases hprologue : prologueCode base a with
    | none =>
        simp only [CodeReq.union, hprologue] at h ⊢
        unfold walkInitEmptyFailNotListFailShortLongCode walkInitEmptyFailOrPrefixCode
        exact CodeReq.union_mono_left a i (CodeReq.union_mono_left a i h)
    | some instr =>
        simp only [CodeReq.union, hprologue] at h ⊢
        exact h)

/-- Expanded precondition for the empty-input path over the full classifier code. -/
theorem walkInitEmptyInputFailureFromPrologueFullCodeNBranch_pre
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase : Word)
    (hprologueCode : base.toNat + 24 < 2 ^ 64)
    (hcode : (base + 24).toNat + 172 < 2 ^ 64) :
    (walkInitEmptyInputFailureFromPrologueFullCodeNBranch base sp0 raVal s0Old s1Old s2Old
      outBase m0 m1 m2 m3 inputBase hprologueCode hcode).pre =
      (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
        walkInitEmptyInputPrologueCarryFrame inputBase outBase) := by
  rfl

/-- Extending code preserves the empty-input branch exits definitionally. -/
theorem walkInitEmptyInputFailureFromPrologueFullCodeNBranch_exits
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase : Word)
    (hprologueCode : base.toNat + 24 < 2 ^ 64)
    (hcode : (base + 24).toNat + 172 < 2 ^ 64) :
    (walkInitEmptyInputFailureFromPrologueFullCodeNBranch base sp0 raVal s0Old s1Old s2Old
      outBase m0 m1 m2 m3 inputBase hprologueCode hcode).exits =
      (walkInitEmptyInputFailureFromPrologueNBranch base sp0 raVal s0Old s1Old s2Old
        outBase m0 m1 m2 m3 inputBase hprologueCode (by omega)).exits := by
  rfl

/-- Empty-input path with the same scratch-register caller frame as the nonempty
    ABI-failure classifier. The precondition is the nonempty classifier frame
    specialized to `listLen = 0` and `input = []`. -/
def walkInitEmptyInputFailureFromPrologueSharedFrameNBranch
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase : Word)
    (t0Old t1Old : Word)
    (hprologueCode : base.toNat + 24 < 2 ^ 64)
    (hcode : (base + 24).toNat + 172 < 2 ^ 64) :
    WP.NBranch base
      ((prologueCode base).union
        (walkInitEmptyFailNotListFailShortLongCode (base + 24))) := by
  let br0 := walkInitEmptyInputFailureFromPrologueFullCodeNBranch base sp0 raVal s0Old s1Old
    s2Old outBase m0 m1 m2 m3 inputBase hprologueCode hcode
  let scratchFrame := walkInitEmptyInputPrologueScratchFrame t0Old t1Old
  let br := WP.CFG.nbranchFrameR br0 scratchFrame
    (walkInitEmptyInputPrologueScratchFrame_pcFree t0Old t1Old)
  have hpre : WP.Entails
      (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
        walkInitAbiFailurePrologueCarryFrame inputBase (0 : Word) t0Old t1Old outBase
          ([] : List Byte))
      br.pre := by
    dsimp [br, br0, scratchFrame, WP.CFG.nbranchFrameR, WP.NBranch.frameR]
    rw [walkInitEmptyInputFailureFromPrologueFullCodeNBranch_pre]
    exact prologuePreAbiFailureEmptyCarry_entails_emptyScratchPre sp0 raVal s0Old s1Old
      s2Old outBase m0 m1 m2 m3 inputBase t0Old t1Old
  wp_rv64_nbranch_weaken_pre_with br, hpre

/-- Expanded shared-frame precondition for the empty-input full-code path. -/
theorem walkInitEmptyInputFailureFromPrologueSharedFrameNBranch_pre
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase : Word)
    (t0Old t1Old : Word)
    (hprologueCode : base.toNat + 24 < 2 ^ 64)
    (hcode : (base + 24).toNat + 172 < 2 ^ 64) :
    (walkInitEmptyInputFailureFromPrologueSharedFrameNBranch base sp0 raVal s0Old s1Old
      s2Old outBase m0 m1 m2 m3 inputBase t0Old t1Old hprologueCode hcode).pre =
      (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
        walkInitAbiFailurePrologueCarryFrame inputBase (0 : Word) t0Old t1Old outBase
          ([] : List Byte)) := by
  rfl

/-- Prologue followed by the ABI-failure classifier. Empty and not-list exits
    expose reason-erased ABI failure posts; short-list and long-list candidates
    remain open for later resolution. -/
def walkInitAbiFailureFromPrologueNBranch
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte)
    (hsalign : inputBase.toNat % 8 = 0) (hoff : 0 < input.length)
    (hover0 : inputBase.toNat + 0 < 2 ^ 64)
    (hvalid0 : isValidByteAccess (inputBase + BitVec.ofNat 64 0) = true)
    (hLen : listLen = BitVec.ofNat 64 input.length)
    (hBound : input.length < 2 ^ 64)
    (hprologueCode : base.toNat + 24 < 2 ^ 64)
    (hcode : (base + 24).toNat + 172 < 2 ^ 64) :
    WP.NBranch base
      ((prologueCode base).union (walkInitEmptyFailNotListFailShortLongCode (base + 24))) := by
  let carryFrame := walkInitAbiFailurePrologueCarryFrame inputBase listLen t0Old t1Old
    outBase input
  let savedFrame := walkInitAbiFailurePrologueSavedFrame sp0 raVal s0Old s1Old s2Old outBase
  let head := prologueCert base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3
  let tail := walkInitEmptyNotListAbiFailureNBranch (base + 24) inputBase listLen raVal
    t0Old t1Old outBase input hsalign hoff hover0 hvalid0 hLen hBound
  have hlink : WP.Entails
      (prologuePost sp0 raVal s0Old s1Old s2Old outBase ** carryFrame)
      (tail.pre ** savedFrame) := by
    dsimp [tail, carryFrame, savedFrame]
    simp only [walkInitEmptyNotListAbiFailureNBranch_pre,
      walkInitEmptyFailNotListFailShortLongOutputNBranch_pre]
    exact prologuePostAbiFailureCarry_entails_preFromPrologue sp0 raVal s0Old s1Old
      s2Old inputBase listLen t0Old t1Old outBase input
  wp_rv64_seq_block_nbranch_framed_disjoint_with
    (prologueCode_disjoint_walkInitEmptyFailNotListFailShortLongCode base
      hprologueCode hcode),
    head, carryFrame,
    (walkInitAbiFailurePrologueCarryFrame_pcFree inputBase listLen t0Old t1Old outBase input),
    tail, savedFrame,
    (walkInitAbiFailurePrologueSavedFrame_pcFree sp0 raVal s0Old s1Old s2Old outBase),
    hlink

/-- Expanded precondition for the prologue-to-ABI-failure classifier. -/
theorem walkInitAbiFailureFromPrologueNBranch_pre
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte)
    (hsalign : inputBase.toNat % 8 = 0) (hoff : 0 < input.length)
    (hover0 : inputBase.toNat + 0 < 2 ^ 64)
    (hvalid0 : isValidByteAccess (inputBase + BitVec.ofNat 64 0) = true)
    (hLen : listLen = BitVec.ofNat 64 input.length)
    (hBound : input.length < 2 ^ 64)
    (hprologueCode : base.toNat + 24 < 2 ^ 64)
    (hcode : (base + 24).toNat + 172 < 2 ^ 64) :
    (walkInitAbiFailureFromPrologueNBranch base sp0 raVal s0Old s1Old s2Old outBase
      m0 m1 m2 m3 inputBase listLen t0Old t1Old input hsalign hoff hover0 hvalid0 hLen
      hBound hprologueCode hcode).pre =
      (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
        walkInitAbiFailurePrologueCarryFrame inputBase listLen t0Old t1Old outBase input) := by
  rfl

/-- Prologue followed by the ABI-failure classifier, with the empty/nonempty
    split selected from the concrete input bytes. Callers supply only static
    length and memory-validity facts; the WP facade chooses the empty path for
    `[]` and the classifier path for nonempty input. -/
def walkInitZeroNonzeroAbiFailureFromPrologueNBranch
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : ∀ i, i < input.length → isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hLen : listLen = BitVec.ofNat 64 input.length)
    (hprologueCode : base.toNat + 24 < 2 ^ 64)
    (hcode : (base + 24).toNat + 172 < 2 ^ 64) :
    WP.NBranch base
      ((prologueCode base).union
        (walkInitEmptyFailNotListFailShortLongCode (base + 24))) := by
  cases input with
  | nil =>
      let br0 := walkInitEmptyInputFailureFromPrologueSharedFrameNBranch base sp0 raVal
        s0Old s1Old s2Old outBase m0 m1 m2 m3 inputBase t0Old t1Old hprologueCode hcode
      have hpre : WP.Entails
          (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
            walkInitAbiFailurePrologueCarryFrame inputBase listLen t0Old t1Old outBase
              ([] : List Byte))
          br0.pre := by
        dsimp [br0]
        rw [walkInitEmptyInputFailureFromPrologueSharedFrameNBranch_pre]
        have hLen0 : listLen = (0 : Word) := by
          simpa using hLen
        subst listLen
        wp_rv64_link
      wp_rv64_nbranch_weaken_pre_with br0, hpre
  | cons b rest =>
      have hoff : 0 < (b :: rest).length := by simp
      have hover0 : inputBase.toNat + 0 < 2 ^ 64 := by
        omega
      have hvalid0 : isValidByteAccess (inputBase + BitVec.ofNat 64 0) = true :=
        hwin 0 hoff
      have hBound : (b :: rest).length < 2 ^ 64 := by
        omega
      exact walkInitAbiFailureFromPrologueNBranch base sp0 raVal s0Old s1Old s2Old
        outBase m0 m1 m2 m3 inputBase listLen t0Old t1Old (b :: rest) hsalign hoff
        hover0 hvalid0 hLen hBound hprologueCode hcode

/-- Fully reduced precondition for the input-indexed empty/nonempty ABI-failure
    facade. It is static and contains no pre-decoded branch/result fact. -/
theorem walkInitZeroNonzeroAbiFailureFromPrologueNBranch_pre
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input : List Byte)
    (hsalign : inputBase.toNat % 8 = 0)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : ∀ i, i < input.length → isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hLen : listLen = BitVec.ofNat 64 input.length)
    (hprologueCode : base.toNat + 24 < 2 ^ 64)
    (hcode : (base + 24).toNat + 172 < 2 ^ 64) :
    (walkInitZeroNonzeroAbiFailureFromPrologueNBranch base sp0 raVal s0Old s1Old s2Old
      outBase m0 m1 m2 m3 inputBase listLen t0Old t1Old input hsalign hover hwin hLen
      hprologueCode hcode).pre =
      (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
        walkInitAbiFailurePrologueCarryFrame inputBase listLen t0Old t1Old outBase input) := by
  cases input with
  | nil => rfl
  | cons b rest => rfl

/-- Prologue followed by the reduced short-list success WP slice.  The prologue
    carries the walk-init/schema resources to its exit; the tail consumes those
    resources and returns the ABI success post while preserving the saved frame. -/
def walkInitShortSuccessFromPrologueCert
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input d0 d1 d2 d3 : List Byte)
    (hsalign : inputBase.toNat % 8 = 0) (hoff : 0 < input.length)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : ∀ i, i < input.length → isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (hLen : listLen = BitVec.ofNat 64 input.length)
    (hprologueCode : base.toNat + 24 < 2 ^ 64)
    (hcode : (base + 24).toNat + 172 + 4 +
      schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    WP.CFG.Cert base (successStatusReturnExit raVal)
      ((prologueCode base).union
        (walkInitShortSuccessResolvedCode (base + 24) (successFieldSpecs d0 d1 d2 d3)))
      (walkInitShortSuccessAbiPost inputBase outBase raVal input d0 d1 d2 d3 **
        walkInitShortSuccessPrologueSavedFrame sp0 raVal s0Old s1Old s2Old) := by
  let carryFrame := walkInitShortSuccessPrologueCarryFrame inputBase listLen t0Old t1Old
    outBase input
  let savedFrame := walkInitShortSuccessPrologueSavedFrame sp0 raVal s0Old s1Old s2Old
  let head := WP.CFG.frameR
    (prologueCert base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3)
    carryFrame
    (walkInitShortSuccessPrologueCarryFrame_pcFree inputBase listLen t0Old t1Old outBase input)
  let tail0 : WP.CFG.Cert (base + 24) (successStatusReturnExit raVal)
      (walkInitShortSuccessResolvedCode (base + 24) (successFieldSpecs d0 d1 d2 d3))
      (walkInitShortSuccessAbiPost inputBase outBase raVal input d0 d1 d2 d3) :=
    WP.CFG.block (WP.Entails.refl _) (by
      simpa [walkInitShortSuccessResolvedCode] using
        walkInitShortSuccessResolved_spec_within (base + 24) inputBase listLen raVal t0Old
          t1Old outBase input d0 d1 d2 d3 hsalign hoff hover hwin hdalign hdov hdval
          hc0 hl0 hc1 hl1 haddr hc3 hl3 hinput hLen hcode)
  let tail := WP.CFG.frameR tail0 savedFrame
    (walkInitShortSuccessPrologueSavedFrame_pcFree sp0 raVal s0Old s1Old s2Old)
  exact WP.CFG.seqDisjoint
    (prologueCode_disjoint_walkInitShortSuccessResolvedCode base
      (successFieldSpecs d0 d1 d2 d3) hprologueCode hcode) head.sound tail
    (by
      dsimp [head, tail, tail0, carryFrame, savedFrame, WP.CFG.frameR, WP.CFG.block,
        WP.Triple.frameR, WP.Triple.ofSpec]
      simpa using prologuePostShortSuccessCarry_entails_resolvedPre sp0 raVal s0Old s1Old s2Old
        inputBase listLen t0Old t1Old outBase input)

/-- Expanded precondition for the prologue-to-short-success certificate. -/
theorem walkInitShortSuccessFromPrologueCert_pre
    (base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 : Word)
    (inputBase listLen t0Old t1Old : Word)
    (input d0 d1 d2 d3 : List Byte)
    (hsalign : inputBase.toNat % 8 = 0) (hoff : 0 < input.length)
    (hover : inputBase.toNat + input.length < 2 ^ 64)
    (hwin : ∀ i, i < input.length → isValidByteAccess (inputBase + BitVec.ofNat 64 i) = true)
    (hdalign : outBase.toNat % 8 = 0)
    (hdov : outBase.toNat + outputSize < 2 ^ 64)
    (hdval : ∀ i, i < outputSize → isValidByteAccess (outBase + BitVec.ofNat 64 i) = true)
    (hc0 : d0.headD 1 ≠ 0) (hl0 : d0.length ≤ 8)
    (hc1 : d1.headD 1 ≠ 0) (hl1 : d1.length ≤ 8)
    (haddr : d2.length = 20)
    (hc3 : d3.headD 1 ≠ 0) (hl3 : d3.length ≤ 8)
    (hinput : input = encode (.list (schemaItems (successFieldSpecs d0 d1 d2 d3))))
    (hLen : listLen = BitVec.ofNat 64 input.length)
    (hprologueCode : base.toNat + 24 < 2 ^ 64)
    (hcode : (base + 24).toNat + 172 + 4 +
      schemaSize (successFieldSpecs d0 d1 d2 d3) + 8 < 2 ^ 64) :
    (walkInitShortSuccessFromPrologueCert base sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2
      m3 inputBase listLen t0Old t1Old input d0 d1 d2 d3 hsalign hoff hover hwin hdalign
      hdov hdval hc0 hl0 hc1 hl1 haddr hc3 hl3 hinput hLen hprologueCode hcode).pre =
      (prologuePre sp0 raVal s0Old s1Old s2Old outBase m0 m1 m2 m3 **
        walkInitShortSuccessPrologueCarryFrame inputBase listLen t0Old t1Old outBase input) := by
  rfl

end WithdrawalDecode

end EvmAsm.Rv64.RLP
