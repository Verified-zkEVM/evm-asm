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

end WithdrawalDecode

end EvmAsm.Rv64.RLP
