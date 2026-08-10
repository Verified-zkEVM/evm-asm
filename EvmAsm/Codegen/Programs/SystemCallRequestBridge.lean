/-
  EvmAsm.Codegen.Programs.SystemCallRequestBridge

  GH #11578 — the request-derive half of the EIP-7002/EIP-7251 seam.

  `derive_withdrawal_requests` and `derive_consolidation_requests` are seven
  instruction ABI shims.  They tail-jump to `stage_system_call`; they do not
  parse, stride through, or copy the return-data buffer.  This module therefore
  proves the pure request framing that surrounds the shims, rather than
  pretending that a machine triple exists for the unproven dispatcher call.

  The reference operation is `process_general_purpose_requests`
  (`Stateless/SpecRef/Fork.lean:493-512`): a successful checked system call
  contributes `0x01 :: return_data` or `0x02 :: return_data` exactly when the
  returned byte list is non-empty.  `encode_execution_requests` in
  `SpecRef/SeamShell.lean` has the same per-kind prefix shape for its typed
  engine-API input, but it is the opposite side of the seam; this file keeps
  the raw execution-derived body opaque, as the reference does.

  ## Residual machine premise

  `stageSystemCallPost` is deliberately a parameter type, not an axiom and not
  a definition claiming what the dispatcher does.  A future `stage_system_call`
  triple must instantiate it with the relation between the four ABI inputs and
  the returned body/status.  The two framing triples below are parametric in
  that post: the framing fact itself is independent of the callee, while the
  post is what a future machine composition will consume.  Status/body are
  output facts, not input-domain gates.
-/

import EvmAsm.Codegen.Programs.SystemCallStaging
import EvmAsm.Stateless.SpecRef.SeamShell

namespace EvmAsm.Codegen.SystemCallRequestBridge

open EvmAsm.Stateless.SpecRef

/-! ## The opaque stage-call boundary -/

/-- The four values handed to `stage_system_call` by each derive shim.

    These are ABI coordinates, not a claim that the callee reads them in a
    particular way.  The machine triple for the callee is the missing premise.
    `outputBuffer` is included because the callee's returned `Bytes` is the
    projection of its captured return-data window at that address. -/
structure StageSystemCallInput where
  predeployCode : Nat
  codeLength : Nat
  executionPayload : Nat
  outputBuffer : Nat
  deriving DecidableEq, Repr

/-- The observable result surfaced by the shared staging seam.

    `status = 0` is the successful checked-system-call arm; nonzero status is
    rejected by the EIP-7002/EIP-7251 callers.  No theorem here identifies the
    bytes or status with the execution: that is exactly the residual callee
    contract recorded in `Progress.Obligations`. -/
structure StageSystemCallOutput where
  returnData : Bytes
  status : Nat
  deriving DecidableEq, Repr

/-- Named residual premise for the unproven `stage_system_call` machine seam.

    Keeping this as a function-valued relation makes the dependency visible at
    every bridge use without introducing an `axiom` or silently treating the
    raw `String` emitter as verified. -/
abbrev StageSystemCallPost :=
  StageSystemCallInput → StageSystemCallOutput → Prop

/-! ## Pure request framing -/

/-- The EIP-7002 request-list type byte. -/
def withdrawalRequestType : Byte := 0x01

/-- The EIP-7251 request-list type byte. -/
def consolidationRequestType : Byte := 0x02

/-- Append one execution-derived request blob iff its return data is non-empty.

    This is the common pure part of `process_general_purpose_requests` for the
    two checked predeploys.  The body is intentionally opaque: fixed widths
    such as 76 and 116 belong to the predeploy output format, not to this
    request-derive operation. -/
def appendDerivedRequest (requests : List Bytes) (requestType : Byte)
    (returnData : Bytes) : List Bytes :=
  requests ++ if returnData.length > 0 then [requestType :: returnData] else []

/-- Withdrawal derivation's pure output projection. -/
def deriveWithdrawalRequestOutput (requests : List Bytes)
    (returnData : Bytes) : List Bytes :=
  appendDerivedRequest requests withdrawalRequestType returnData

/-- Consolidation derivation's pure output projection. -/
def deriveConsolidationRequestOutput (requests : List Bytes)
    (returnData : Bytes) : List Bytes :=
  appendDerivedRequest requests consolidationRequestType returnData

/-! ## The two framing triples

    These are deliberately parallel.  Their only difference is the request
    type byte; neither carries an input-domain restriction.  `h_stage` is a
    dependency on the future machine seam, not a precondition selecting an
    execution outcome. -/

/-- Pure request-derive triple for `derive_withdrawal_requests`.

    Given any future contract for the tail-called staging seam, the derive
    result contributes exactly the EIP-7002 type-prefixed body on the success
    path, and contributes no blob for an empty return-data list.  This proves
    framing only; it does not prove `stage_system_call` or the predeploy. -/
theorem deriveWithdrawalRequests_request_derive_triple
    (stagePost : StageSystemCallPost) :
    ∀ (input : StageSystemCallInput) (output : StageSystemCallOutput)
      (requests : List Bytes),
      stagePost input output →
      (output.status = 0 ∧
        deriveWithdrawalRequestOutput requests output.returnData =
          requests ++
            (if output.returnData.length > 0 then
              [withdrawalRequestType :: output.returnData] else [])) ∨
        output.status ≠ 0 := by
  intro input output requests h_stage
  by_cases h_status : output.status = 0
  · left
    refine ⟨h_status, ?_⟩
    simp [deriveWithdrawalRequestOutput, appendDerivedRequest]
  · exact Or.inr h_status

/-- Pure request-derive triple for `derive_consolidation_requests`.

    This has the same hypotheses and post shape as the withdrawal triple.  The
    equality of shapes is intentional: only the EIP-7251 type byte changes. -/
theorem deriveConsolidationRequests_request_derive_triple
    (stagePost : StageSystemCallPost) :
    ∀ (input : StageSystemCallInput) (output : StageSystemCallOutput)
      (requests : List Bytes),
      stagePost input output →
      (output.status = 0 ∧
        deriveConsolidationRequestOutput requests output.returnData =
          requests ++
            (if output.returnData.length > 0 then
              [consolidationRequestType :: output.returnData] else [])) ∨
        output.status ≠ 0 := by
  intro input output requests h_stage
  by_cases h_status : output.status = 0
  · left
    refine ⟨h_status, ?_⟩
    simp [deriveConsolidationRequestOutput, appendDerivedRequest]
  · exact Or.inr h_status

/-! ## The SeamShell encoder projections

    The projection and matching lemmas below tie the raw-body framing above to
    the corresponding halves of `encode_execution_requests`.  The matching
    lemmas intentionally take the body/list correspondence as a hypothesis:
    `SpecRef` keeps fixed-width request fields as untyped `Bytes`, so a 20/48/8
    or 20/48/48 width theorem would be a new input-domain claim rather than a
    fact about this derive seam. -/

/-- The withdrawal arm of `encode_execution_requests`, exposed by projection. -/
def encodeWithdrawalRequestHalf (requests : ExecutionRequests) : List Bytes :=
  if requests.withdrawals.isEmpty then [] else
    [withdrawalRequestType :: requests.withdrawals.flatMap _encode_withdrawal]

/-- The consolidation arm of `encode_execution_requests`, exposed by projection. -/
def encodeConsolidationRequestHalf (requests : ExecutionRequests) : List Bytes :=
  if requests.consolidations.isEmpty then [] else
    [consolidationRequestType :: requests.consolidations.flatMap _encode_consolidation]

/-- `encode_execution_requests` written as its five request arms, with the two
    execution-derived arms named above.  This is only a projection of the
    SeamShell definition; it does not parse or validate a returned body. -/
def encodeExecutionRequestsRequestArms (requests : ExecutionRequests) : List Bytes :=
  (if requests.deposits.isEmpty then [] else
    [0x00 :: (requests.deposits.flatMap _encode_deposit)])
  ++ encodeWithdrawalRequestHalf requests
  ++ encodeConsolidationRequestHalf requests
  ++ (if requests.builderDeposits.isEmpty then [] else
    [0x03 :: (requests.builderDeposits.flatMap _encode_builder_deposit)])
  ++ (if requests.builderExits.isEmpty then [] else
    [0x04 :: (requests.builderExits.flatMap _encode_builder_exit)])

theorem encodeExecutionRequests_eq_request_arms
    (requests : ExecutionRequests) :
    encodeExecutionRequestsRequestArms requests =
      encode_execution_requests requests := by
  rfl

theorem encodeExecutionRequests_withdrawal_half_eq
    (requests : ExecutionRequests) :
    encodeWithdrawalRequestHalf requests =
      (if requests.withdrawals.isEmpty then [] else
        [0x01 :: requests.withdrawals.flatMap _encode_withdrawal]) := by
  rfl

theorem encodeExecutionRequests_consolidation_half_eq
    (requests : ExecutionRequests) :
    encodeConsolidationRequestHalf requests =
      (if requests.consolidations.isEmpty then [] else
        [0x02 :: requests.consolidations.flatMap _encode_consolidation]) := by
  rfl

/-- A withdrawal body that is known to be the encoded withdrawal list, together
    with the nonempty/empty correspondence, is exactly the encoder's
    withdrawal arm.  The two hypotheses are output-shape facts; they are not
    silently promoted to an input-domain restriction on the derive shim. -/
theorem deriveWithdrawalRequestOutput_matches_encode_half
    (requests : ExecutionRequests) (body : Bytes)
    (h_body : body = requests.withdrawals.flatMap _encode_withdrawal)
    (h_nonempty : body.length > 0 ↔ ¬ requests.withdrawals.isEmpty) :
    deriveWithdrawalRequestOutput [] body =
      encodeWithdrawalRequestHalf requests := by
  subst body
  cases h_withdrawals : requests.withdrawals with
  | nil =>
    simp [deriveWithdrawalRequestOutput, appendDerivedRequest,
      encodeWithdrawalRequestHalf, h_withdrawals]
  | cons withdrawal withdrawals =>
    have h_len :
        (requests.withdrawals.flatMap _encode_withdrawal).length > 0 :=
      h_nonempty.mpr (by simp [h_withdrawals])
    rw [h_withdrawals] at h_len
    simp only [deriveWithdrawalRequestOutput, appendDerivedRequest,
      List.nil_append]
    rw [if_pos h_len]
    simp [encodeWithdrawalRequestHalf, h_withdrawals]

/-- Consolidation counterpart of
    `deriveWithdrawalRequestOutput_matches_encode_half`, with the identical
    hypothesis and postcondition shape and only the EIP-7251 arm changed. -/
theorem deriveConsolidationRequestOutput_matches_encode_half
    (requests : ExecutionRequests) (body : Bytes)
    (h_body : body = requests.consolidations.flatMap _encode_consolidation)
    (h_nonempty : body.length > 0 ↔ ¬ requests.consolidations.isEmpty) :
    deriveConsolidationRequestOutput [] body =
      encodeConsolidationRequestHalf requests := by
  subst body
  cases h_consolidations : requests.consolidations with
  | nil =>
    simp [deriveConsolidationRequestOutput, appendDerivedRequest,
      encodeConsolidationRequestHalf, h_consolidations]
  | cons consolidation consolidations =>
    have h_len :
        (requests.consolidations.flatMap _encode_consolidation).length > 0 :=
      h_nonempty.mpr (by simp [h_consolidations])
    rw [h_consolidations] at h_len
    simp only [deriveConsolidationRequestOutput, appendDerivedRequest,
      List.nil_append]
    rw [if_pos h_len]
    simp [encodeConsolidationRequestHalf, h_consolidations]

/-! ## Small executable witnesses -/

#guard withdrawalRequestType == (0x01 : Byte)
#guard consolidationRequestType == (0x02 : Byte)
#guard deriveWithdrawalRequestOutput [] [] == []
#guard deriveWithdrawalRequestOutput [] [0xAA] == [[0x01, 0xAA]]
#guard deriveConsolidationRequestOutput [] [] == []
#guard deriveConsolidationRequestOutput [] [0xBB] == [[0x02, 0xBB]]

end EvmAsm.Codegen.SystemCallRequestBridge
