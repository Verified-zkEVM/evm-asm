/-
  EvmAsm.Rv64.RLP.WithdrawalDecodeFailureWP

  Semantic failure adapters for the withdrawal decoder WP calculus.  The exact
  control-flow reason remains in a scratch frame; the public ABI component only
  states that the pure `decodeWithdrawal` result is failure.
-/

import EvmAsm.Rv64.RLP.WithdrawalDecode

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

namespace WithdrawalDecode

/-- A byte/string RLP prefix cannot decode as a list. -/
theorem decodeAux_ne_list_of_head_lt_c0
    (fuel : Nat) (pfx : Byte) (rest leftover : List Byte) (items : List RLPItem)
    (h : BitVec.ult (pfx.zeroExtend 64) (0xc0 : Word) = true) :
    decodeAux (fuel + 1) (pfx :: rest) ≠ some (.list items, leftover) := by
  have hp : pfx.toNat < 192 := by
    simp only [BitVec.ult, decide_eq_true_eq, show (0xc0 : Word).toNat = 192 from by decide,
      BitVec.toNat_setWidth] at h
    have hb : pfx.toNat < 2 ^ 64 := by
      have := pfx.isLt
      omega
    rw [Nat.mod_eq_of_lt hb] at h
    exact h
  intro hdec
  unfold decodeAux at hdec
  by_cases h80 : pfx.toNat < 128
  · simp [h80] at hdec
  · by_cases hB7 : pfx.toNat ≤ 183
    · simp [h80, hB7] at hdec
      cases ht : takeBytes rest (pfx.toNat - 128) with
      | none => simp [ht] at hdec
      | some pair =>
          cases pair with
          | mk data rest' =>
              simp [ht] at hdec
              cases data with
              | nil => simp at hdec
              | cons b tail =>
                  cases tail with
                  | nil => by_cases hb : b.toNat < 128 <;> simp [hb] at hdec
                  | cons _ _ => simp at hdec
    · have hBF : pfx.toNat ≤ 191 := by omega
      simp [h80, hB7, hBF] at hdec
      cases hr : readLength rest (pfx.toNat - 183) with
      | none => simp [hr] at hdec
      | some pair =>
          cases pair with
          | mk lenVal rest' =>
              by_cases hlen : lenVal ≤ 55
              · simp [hr, hlen] at hdec
              · simp [hr, hlen] at hdec
                cases ht : takeBytes rest' lenVal with
                | none => simp [ht] at hdec
                | some pair2 =>
                    cases pair2 with
                    | mk _ _ => simp [ht] at hdec

/-- A complete RLP decode whose first byte is below `0xc0` cannot be a list. -/
theorem decodeFully_ne_list_of_head_lt_c0
    (pfx : Byte) (rest : List Byte) (items : List RLPItem)
    (h : BitVec.ult (pfx.zeroExtend 64) (0xc0 : Word) = true) :
    decodeFully (pfx :: rest) ≠ some (.list items) := by
  intro hfull
  have hdecode : decode (pfx :: rest) = some (.list items, []) :=
    (decodeFully_eq_some_iff (pfx :: rest) (.list items)).1 hfull
  rw [decode_cons_eq_decodeAux_fuel] at hdecode
  exact decodeAux_ne_list_of_head_lt_c0 (2 * rest.length + 1) pfx rest [] items h hdecode

/-- A withdrawal is encoded as an RLP list, so any byte/string prefix is a
    reason-erased semantic failure. -/
theorem decodeWithdrawal_none_of_head_lt_c0
    (pfx : Byte) (rest : List Byte)
    (h : BitVec.ult (pfx.zeroExtend 64) (0xc0 : Word) = true) :
    decodeWithdrawal (pfx :: rest) = none := by
  unfold decodeWithdrawal
  generalize hfull : decodeFully (pfx :: rest) = decoded
  cases decoded with
  | none => rfl
  | some item =>
      cases item with
      | bytes _ => rfl
      | list items =>
          exfalso
          exact decodeFully_ne_list_of_head_lt_c0 pfx rest items h hfull

/-- The shallow empty-input split has a semantic failure head exit and one
    syntactic nonzero fall-through exit. -/
theorem walkInitEmptyInputFailureNBranch_exits
    (base inputBase outBase raVal statusOld : Word) :
    (walkInitEmptyInputFailureNBranch base inputBase outBase raVal statusOld).exits =
      [ (failStatusReturnExit raVal, emptyInputFailurePost inputBase outBase raVal)
      , (base + 4,
          walkInitNonzeroOpenStatusPost (0 : Word) raVal statusOld **
            emptyInputAbiFrame inputBase outBase)
      ] := by
  rfl

/-- The nonzero fall-through exit of the empty-input specialization is
    contradictory because it carries `0 != 0`. -/
theorem walkInitEmptyInputNonzeroExit_contradicts
    (inputBase outBase raVal statusOld : Word) :
    ∀ h,
      (walkInitNonzeroOpenStatusPost (0 : Word) raVal statusOld **
        emptyInputAbiFrame inputBase outBase) h → False := by
  intro h hp
  unfold walkInitNonzeroOpenStatusPost walkInitNonzeroPost at hp
  rcases hp with ⟨hMain, _hFrame, _hdFrame, _hunionFrame, hMain_prop, _hFrame_prop⟩
  rcases hMain_prop with ⟨hRegs, _hFail, _hdFail, _hunionFail, hRegs_prop, _hFail_prop⟩
  rcases hRegs_prop with ⟨_hRegs, hTail, _hdTail, _hunionTail, _hRegs_prop, hTail_prop⟩
  rcases hTail_prop with ⟨_hX0, _hPure, _hdPure, _hunionPure, _hX0_prop, hPure_prop⟩
  unfold EvmAsm.Rv64.pure at hPure_prop
  exact hPure_prop.2 rfl

/-- Resolved empty-input certificate: the impossible nonzero exit is closed by
    contradiction, leaving the semantic failure post as the only result. -/
def walkInitEmptyInputFailureCert
    (base inputBase outBase raVal statusOld : Word) :
    WP.CFG.Cert base (failStatusReturnExit raVal) (walkInitEmptyFailStatusCode base)
      (emptyInputFailurePost inputBase outBase raVal) := by
  let br := walkInitEmptyInputFailureNBranch base inputBase outBase raVal statusOld
  wp_rv64_nbranch_join2_resolve_first_auto br,
    (walkInitEmptyInputFailureNBranch_exits base inputBase outBase raVal statusOld),
    (emptyInputFailurePost inputBase outBase raVal),
    (walkInitEmptyInputNonzeroExit_contradicts inputBase outBase raVal statusOld)

/-- The resolved empty-input certificate reduces to the shallow walk-init
    empty-input precondition. -/
theorem walkInitEmptyInputFailureCert_pre
    (base inputBase outBase raVal statusOld : Word) :
    (walkInitEmptyInputFailureCert base inputBase outBase raVal statusOld).pre =
      (walkInitEmptyInputFailureNBranch base inputBase outBase raVal statusOld).pre := by
  rfl

/-- Scratch facts preserved by the empty-input failure case after exposing the
    public ABI failure component. -/
def walkInitEmptyFailAbiFrame (listLen t0Old t1Old : Word) : Assertion :=
  ((.x11 ↦ᵣ listLen) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
    ⌜listLen = (0 : Word)⌝)

/-- Scratch facts preserved by the not-list failure case after exposing the
    public ABI failure component. -/
def walkInitNotListFailAbiFrame
    (listBase listLen : Word) (listBytes : List Byte)
    (listOff : Nat) (hoff : listOff < listBytes.length) : Assertion :=
  ((.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
    (.x5 ↦ᵣ walkInitPrefixWord listBytes listOff hoff) **
    (.x6 ↦ᵣ (0xc0 : Word)) **
    ⌜listLen ≠ (0 : Word)⌝ **
    ⌜BitVec.ult (walkInitPrefixWord listBytes listOff hoff) (0xc0 : Word)⌝)

theorem walkInitEmptyFailOutputPost_entails_abiFailureFrame
    (inputBase listLen raVal t0Old t1Old outBase : Word) (input : List Byte)
    (hLen : listLen = BitVec.ofNat 64 input.length)
    (hBound : input.length < 2 ^ 64) :
    WP.Entails
      (walkInitEmptyFailOutputPost inputBase listLen raVal t0Old t1Old outBase input)
      (abiPost inputBase outBase raVal input ** walkInitEmptyFailAbiFrame listLen t0Old t1Old) := by
  intro h hp
  have hpCase := hp
  unfold walkInitEmptyFailOutputPost walkInitEmptyFailStatusPost failStatusReturnPost
    statusReturnPost walkInitZeroPost at hpCase
  rcases hpCase with ⟨hA, _hOut, _hdOut, _hunionOut, hA_prop, _hOut_prop⟩
  rcases hA_prop with ⟨hB, _hBytes, _hdBytes, _hunionBytes, hB_prop, _hBytes_prop⟩
  rcases hB_prop with ⟨hC, _hX6, _hdX6, _hunionX6, hC_prop, _hX6_prop⟩
  rcases hC_prop with ⟨_hX1, _hX10, _hdX10, _hunionX10, _hX1_prop, _hX10_prop⟩
  have hX6Pure := _hX6_prop
  extract_pure hX6Pure
  have hzero : listLen = (0 : Word) := hX6Pure.1
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
  unfold walkInitEmptyFailOutputPost walkInitEmptyFailStatusPost failStatusReturnPost
    statusReturnPost walkInitZeroPost at hp
  unfold abiPost walkInitEmptyFailAbiFrame
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
  xperm_hyp hp

theorem walkInitNotListFailOutputPost_entails_abiFailureFrame_zeroOff
    (inputBase listLen raVal outBase : Word) (input : List Byte)
    (hoff : 0 < input.length) :
    WP.Entails
      (walkInitNotListFailOutputPost inputBase listLen raVal outBase input 0 hoff)
      (abiPost inputBase outBase raVal input **
        walkInitNotListFailAbiFrame inputBase listLen input 0 hoff) := by
  intro h hp
  have hpCase := hp
  unfold walkInitNotListFailOutputPost walkInitPrefixNotListFailStatusPost
    walkInitPrefixNotListFailStatusFrame walkInitPrefixWord at hpCase
  rcases hpCase with ⟨hMain, _hOut, _hdOut, _hunionOut, hMain_prop, _hOut_prop⟩
  rcases hMain_prop with ⟨_hFail, hFrame, _hdFrame, _hunionFrame, _hFail_prop, hFrame_prop⟩
  rcases hFrame_prop with ⟨_hFrameHead, hFrameTail, _hdFrameTail, _hunionFrameTail,
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
  unfold walkInitNotListFailOutputPost walkInitPrefixNotListFailStatusPost
    walkInitPrefixNotListFailStatusFrame failStatusReturnPost statusReturnPost walkInitPrefixWord at hp
  unfold abiPost walkInitNotListFailAbiFrame walkInitPrefixWord
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
  xperm_hyp hp

/-- Walk-init classifier whose empty and not-list exits expose the semantic ABI
    failure post, while short-list and long-list candidates remain open. -/
def walkInitEmptyNotListAbiFailureNBranch
    (base inputBase listLen raVal t0Old t1Old outBase : Word)
    (input : List Byte)
    (hsalign : inputBase.toNat % 8 = 0) (hoff : 0 < input.length)
    (hover0 : inputBase.toNat + 0 < 2 ^ 64)
    (hvalid0 : isValidByteAccess (inputBase + BitVec.ofNat 64 0) = true)
    (hLen : listLen = BitVec.ofNat 64 input.length)
    (hBound : input.length < 2 ^ 64) :
    WP.NBranch base (walkInitEmptyFailNotListFailShortLongCode base) :=
  walkInitEmptyFailNotListFailShortLongOutputCaseNBranch base inputBase listLen raVal
    t0Old t1Old outBase input 0 hsalign hoff hover0 hvalid0
    (abiPost inputBase outBase raVal input ** walkInitEmptyFailAbiFrame listLen t0Old t1Old)
    (abiPost inputBase outBase raVal input ** walkInitNotListFailAbiFrame inputBase listLen input 0 hoff)
    (walkInitShortListOutputPost inputBase listLen raVal outBase input 0 hoff)
    (walkInitLongListOutputPost inputBase listLen raVal outBase input 0 hoff)
    (walkInitEmptyFailOutputPost_entails_abiFailureFrame inputBase listLen raVal t0Old t1Old
      outBase input hLen hBound)
    (walkInitNotListFailOutputPost_entails_abiFailureFrame_zeroOff inputBase listLen raVal
      outBase input hoff)
    (WP.Entails.refl _)
    (WP.Entails.refl _)

theorem walkInitEmptyNotListAbiFailureNBranch_pre
    (base inputBase listLen raVal t0Old t1Old outBase : Word)
    (input : List Byte)
    (hsalign : inputBase.toNat % 8 = 0) (hoff : 0 < input.length)
    (hover0 : inputBase.toNat + 0 < 2 ^ 64)
    (hvalid0 : isValidByteAccess (inputBase + BitVec.ofNat 64 0) = true)
    (hLen : listLen = BitVec.ofNat 64 input.length)
    (hBound : input.length < 2 ^ 64) :
    (walkInitEmptyNotListAbiFailureNBranch base inputBase listLen raVal t0Old t1Old outBase
      input hsalign hoff hover0 hvalid0 hLen hBound).pre =
      (walkInitEmptyFailNotListFailShortLongOutputNBranch base inputBase listLen raVal t0Old
        t1Old outBase input 0 hsalign hoff hover0 hvalid0).pre := by
  rfl

theorem walkInitEmptyNotListAbiFailureNBranch_exits
    (base inputBase listLen raVal t0Old t1Old outBase : Word)
    (input : List Byte)
    (hsalign : inputBase.toNat % 8 = 0) (hoff : 0 < input.length)
    (hover0 : inputBase.toNat + 0 < 2 ^ 64)
    (hvalid0 : isValidByteAccess (inputBase + BitVec.ofNat 64 0) = true)
    (hLen : listLen = BitVec.ofNat 64 input.length)
    (hBound : input.length < 2 ^ 64) :
    (walkInitEmptyNotListAbiFailureNBranch base inputBase listLen raVal t0Old t1Old outBase
      input hsalign hoff hover0 hvalid0 hLen hBound).exits =
      [ (failStatusReturnExit raVal,
          abiPost inputBase outBase raVal input ** walkInitEmptyFailAbiFrame listLen t0Old t1Old)
      , (failStatusReturnExit raVal,
          abiPost inputBase outBase raVal input **
            walkInitNotListFailAbiFrame inputBase listLen input 0 hoff)
      , (base + 124,
          walkInitShortListOutputPost inputBase listLen raVal outBase input 0 hoff)
      , (base + 28,
          walkInitLongListOutputPost inputBase listLen raVal outBase input 0 hoff)
      ] := by
  rfl

end WithdrawalDecode

end EvmAsm.Rv64.RLP
