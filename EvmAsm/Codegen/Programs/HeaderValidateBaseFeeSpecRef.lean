/-
  EvmAsm.Codegen.Programs.HeaderValidateBaseFeeSpecRef

  SpecRef-semantic vocabulary for the K74 `header_validate_base_fee`
  attribution layer (issue #12346; an increment on #12762, whose machine-layer
  spec `header_validate_base_fee_spec_within` ends in a bare status
  disjunction over free byte-list parameters, with no reference-semantics
  content).

  Contents: the expected-fee recurrence (`hvbfExpected`, the pure content of
  the reference `calculate_base_fee_per_gas` after its gas-limit check) and
  its 32-byte encoding (`hvbfExpectedBytes`), the bridge lemma `hvbf_bridge`,
  the isolated reference base-fee check `hvbfSpecRefBaseFeeCheck`, and its
  ok / mismatch evaluation lemmas.  The mismatch arm is attributed to
  `.invalidBlock "base fee mismatch"` — never "gas limit out of bounds",
  which is the reference's *earlier* gas-limit check (`check_gas_limit`
  inside `calculate_base_fee_per_gas`) and a different guest routine's
  status.

  The Route-B K73 premise shape, the machine adapter, and the attributed
  whole-routine theorem live in
  `HeaderValidateBaseFeeSpecRefCompose.lean`.
-/

module

public import EvmAsm.Rv64.Basic
public import EvmAsm.Stateless.SpecRef.Crypto
public import EvmAsm.Stateless.SpecRef.WideFeeArithmetic
meta import EvmAsm.Rv64.Basic
meta import EvmAsm.Stateless.SpecRef.Crypto
meta import EvmAsm.Stateless.SpecRef.WideFeeArithmetic

@[expose] public section

namespace EvmAsm.Codegen.HeaderValidateBaseFeeSpecRef

open EvmAsm.Rv64
open EvmAsm.Stateless.SpecRef

/-- The expected base fee: the reference EIP-1559 recurrence
    (`SpecRef.baseFeeRecurrenceWide`, the pure content of
    `calculate_base_fee_per_gas` after its gas-limit check) at the parent
    values. -/
abbrev hvbfExpected (gasLimit gasUsed : Word) (parentFeeBytes : List (BitVec 8)) : Nat :=
  baseFeeRecurrenceWide gasUsed.toNat (gasLimit.toNat / 2) (bytesBEtoNat parentFeeBytes)

/-- The 32-byte big-endian encoding of the expected base fee — the content
    K73 delivers into the `hvbf_expected` scratch on success. -/
abbrev hvbfExpectedBytes (gasLimit gasUsed : Word) (parentFeeBytes : List (BitVec 8)) :
    List (BitVec 8) :=
  natToBytesBE 32 (hvbfExpected gasLimit gasUsed parentFeeBytes)

/-- The bridge: when the reference's gas-limit check passes,
    `calculate_base_fee_per_gas` returns exactly the recurrence value. -/
theorem hvbf_bridge (blockGasLimit : Nat) (parentGasLimit parentGasUsed : Word)
    (parentFeeBytes : List (BitVec 8))
    (hcheck : check_gas_limit blockGasLimit parentGasLimit.toNat = true) :
    calculate_base_fee_per_gas blockGasLimit parentGasLimit.toNat parentGasUsed.toNat
        (bytesBEtoNat parentFeeBytes) =
      .ok (hvbfExpected parentGasLimit parentGasUsed parentFeeBytes) := by
  unfold calculate_base_fee_per_gas hvbfExpected baseFeeRecurrenceWide
    baseFeeIncreaseDelta baseFeeDecreaseDelta
  rw [hcheck]
  simp
  split
  · rfl
  · split <;> rfl

/-- The reference `validate_header` base-fee check, isolated: compute via
    `calculate_base_fee_per_gas` (propagating its gas-limit-check throw) and
    compare the 32-byte big-endian encodings (the guest's own operation;
    below 2^256 it coincides with the reference's `Uint` comparison). -/
def hvbfSpecRefBaseFeeCheck (blockGasLimit : Nat) (parentGasLimit parentGasUsed : Word)
    (parentFeeBytes hdrFeeBytes : List (BitVec 8)) : Except SpecError Unit :=
  match calculate_base_fee_per_gas blockGasLimit parentGasLimit.toNat
      parentGasUsed.toNat (bytesBEtoNat parentFeeBytes) with
  | .error e => .error e
  | .ok expected =>
      if natToBytesBE 32 expected = hdrFeeBytes then .ok ()
      else .error (.invalidBlock "base fee mismatch")

/-- Match arm: the gas-limit check passes and the claimed fee IS the expected
    encoding, so the reference's base-fee check accepts. -/
theorem hvbfSpecRefBaseFeeCheck_ok (blockGasLimit : Nat)
    (parentGasLimit parentGasUsed : Word)
    (parentFeeBytes hdrFeeBytes : List (BitVec 8))
    (hcheck : check_gas_limit blockGasLimit parentGasLimit.toNat = true)
    (hmatch : hdrFeeBytes =
        hvbfExpectedBytes parentGasLimit parentGasUsed parentFeeBytes) :
    hvbfSpecRefBaseFeeCheck blockGasLimit parentGasLimit parentGasUsed
        parentFeeBytes hdrFeeBytes = .ok () := by
  unfold hvbfSpecRefBaseFeeCheck
  rw [hvbf_bridge blockGasLimit parentGasLimit parentGasUsed parentFeeBytes hcheck]
  show (if hvbfExpectedBytes parentGasLimit parentGasUsed parentFeeBytes =
      hdrFeeBytes then Except.ok () else Except.error (SpecError.invalidBlock "base fee mismatch")) =
    Except.ok ()
  rw [if_pos hmatch.symm]

/-- Mismatch arm: the gas-limit check passes and the claimed fee differs —
    the reference raises `.invalidBlock "base fee mismatch"`. -/
theorem hvbfSpecRefBaseFeeCheck_mismatch (blockGasLimit : Nat)
    (parentGasLimit parentGasUsed : Word)
    (parentFeeBytes hdrFeeBytes : List (BitVec 8))
    (hcheck : check_gas_limit blockGasLimit parentGasLimit.toNat = true)
    (hne : hdrFeeBytes ≠
        hvbfExpectedBytes parentGasLimit parentGasUsed parentFeeBytes) :
    hvbfSpecRefBaseFeeCheck blockGasLimit parentGasLimit parentGasUsed
        parentFeeBytes hdrFeeBytes = .error (.invalidBlock "base fee mismatch") := by
  unfold hvbfSpecRefBaseFeeCheck
  rw [hvbf_bridge blockGasLimit parentGasLimit parentGasUsed parentFeeBytes hcheck]
  show (if hvbfExpectedBytes parentGasLimit parentGasUsed parentFeeBytes =
      hdrFeeBytes then Except.ok () else Except.error (SpecError.invalidBlock "base fee mismatch")) =
    Except.error (SpecError.invalidBlock "base fee mismatch")
  rw [if_neg (fun h => hne h.symm)]

/-- The two attributions can never collide: the base-fee mismatch raise is a
    different `SpecError` from the gas-limit raise (which the reference makes
    earlier, inside `calculate_base_fee_per_gas`). -/
theorem hvbfSpecRef_baseFeeMismatch_ne_gasLimit :
    SpecError.invalidBlock "base fee mismatch" ≠
      SpecError.invalidBlock "gas limit out of bounds" := by
  decide

#print axioms hvbf_bridge
#print axioms hvbfSpecRefBaseFeeCheck_ok
#print axioms hvbfSpecRefBaseFeeCheck_mismatch

end EvmAsm.Codegen.HeaderValidateBaseFeeSpecRef
