/-
  EvmAsm.Codegen.Programs.ExecutionRequestsHashVal

  GH #11578 rescope — validation vocabulary for `execution_requests_hash`.

  Call-graph finding (issue #11578): `derive_withdrawal_requests` /
  `derive_consolidation_requests` are NOT leaves — each is a 7-insn
  `JAL x0` tail into `stage_system_call` → `runtime_dispatcher_call`.
  Maintainer-endorsed retarget is this routine's divisibility/cap gates.

  Anchor: `SszCodec.deserializeAux` fixed-list arm, NOT `compute_requests_hash`.
  Strides/caps pinned by `RequestsHashParams` against SpecRef SSZ types.
  Hash half (`erh_hash_one` + `zkvm_sha256`) is a separate residual row.
-/

import EvmAsm.Rv64.Instructions
import EvmAsm.Rv64.RemuNat
import EvmAsm.Codegen.Programs.RequestsHashParams
import EvmAsm.Evm64.EvmWordArith.MultiLimb

namespace EvmAsm.Codegen.ExecutionRequestsHashVal

open EvmAsm.Rv64
open EvmAsm.Evm64.EvmWord
open EvmAsm.Stateless.SpecRef

/-! ## Pure model

    Guest per kind (RequestsHash.lean validation prefix):
      sub t0, hi, lo
      li  t1, stride
      remu t2, t0, t1 ; bnez t2, .Lerh_fail
      divu t2, t0, t1
      li  t3, cap
      bltu t3, t2, .Lerh_fail     -- taken iff cap < count iff count > cap

    Accept: `bodyLen % stride = 0 ∧ bodyLen / stride ≤ cap`. -/

/-- One SSZ fixed-list body is well-formed for `stride`/`cap`. -/
def fixedListOk (bodyLen stride cap : Nat) : Prop :=
  bodyLen % stride = 0 ∧ bodyLen / stride ≤ cap

/-- Five bodies between consecutive SSZ offsets. -/
structure ErhBodies where
  depositLen : Nat
  withdrawalLen : Nat
  consolidationLen : Nat
  builderDepositLen : Nat
  builderExitLen : Nat

/-- Guest validation over the five body lengths (SpecRef strides/caps). -/
def erhValidationOk (b : ErhBodies) : Prop :=
  fixedListOk b.depositLen
      (SszType.fixedSize sszDepositRequestType)
      MAX_DEPOSIT_REQUESTS_PER_PAYLOAD ∧
  fixedListOk b.withdrawalLen
      (SszType.fixedSize sszWithdrawalRequestType)
      MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD ∧
  fixedListOk b.consolidationLen
      (SszType.fixedSize sszConsolidationRequestType)
      MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD ∧
  fixedListOk b.builderDepositLen
      (SszType.fixedSize sszBuilderDepositRequestType)
      MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD ∧
  fixedListOk b.builderExitLen
      (SszType.fixedSize sszBuilderExitRequestType)
      MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD

private theorem fixedListOk_zero (stride cap : Nat) : fixedListOk 0 stride cap :=
  ⟨Nat.zero_mod stride, by simp [Nat.zero_div]⟩

/-- coverRef: non-empty deposit body (len=192=1×stride) + empty others.
    Empty-only would be one-level vacuous; this is a real payload. -/
theorem erh_validation_precondition_reachable :
    ∃ b : ErhBodies, erhValidationOk b := by
  refine ⟨⟨192, 0, 0, 0, 0⟩, ?_⟩
  -- Strides/caps from SpecRef (pinned by RequestsHashParams #guards).
  have hs : SszType.fixedSize sszDepositRequestType = 192 := by decide
  have hc : MAX_DEPOSIT_REQUESTS_PER_PAYLOAD = 8192 := by decide
  refine ⟨?dep, fixedListOk_zero _ _, fixedListOk_zero _ _,
    fixedListOk_zero _ _, fixedListOk_zero _ _⟩
  simp only [fixedListOk, hs, hc]
  exact ⟨by decide, by decide⟩

/-- Word-level gate matching guest REMU/DIVU/BLTU polarity. -/
def fixedListOkW (bodyLenW strideW capW : Word) : Prop :=
  bodyLenW.toNat % strideW.toNat = 0 ∧
  bodyLenW.toNat / strideW.toNat ≤ capW.toNat

private theorem not_ult_iff_le (a b : Word) :
    ¬ BitVec.ult a b ↔ b.toNat ≤ a.toNat := by
  constructor
  · intro h
    have : ¬ a.toNat < b.toNat := by
      intro hlt
      exact h (by simpa [BitVec.ult] using hlt)
    omega
  · intro hle hult
    have : a.toNat < b.toNat := by simpa [BitVec.ult] using hult
    omega

private theorem ult_iff_lt (a b : Word) :
    BitVec.ult a b ↔ a.toNat < b.toNat := by
  simp [BitVec.ult]

/-- Bridge from guest REMU=0 and ¬BLTU(cap, count) to the Nat predicate. -/
theorem fixedListOkW_of_remu_divu
    (bodyLenW strideW capW : Word)
    (hstride : strideW ≠ 0)
    (hrem : rv64_remu bodyLenW strideW = 0)
    (hcap : ¬ BitVec.ult capW (rv64_divu bodyLenW strideW)) :
    fixedListOkW bodyLenW strideW capW := by
  refine ⟨(remu_eq_zero_iff_mod_eq_zero bodyLenW strideW hstride).1 hrem, ?_⟩
  have hdiv := rv64_divu_toNat bodyLenW strideW hstride
  have hle := (not_ult_iff_le capW (rv64_divu bodyLenW strideW)).1 hcap
  rwa [hdiv] at hle

/-- Reject polarity: remu ≠ 0. -/
theorem fixedListOkW_not_of_remu_ne
    (bodyLenW strideW capW : Word)
    (hstride : strideW ≠ 0)
    (hrem : rv64_remu bodyLenW strideW ≠ 0) :
    ¬ fixedListOkW bodyLenW strideW capW := by
  intro h
  exact (remu_ne_zero_iff_mod_ne_zero bodyLenW strideW hstride).1 hrem h.1

/-- Reject polarity: count > cap (BLTU taken). -/
theorem fixedListOkW_not_of_cap_lt
    (bodyLenW strideW capW : Word)
    (hstride : strideW ≠ 0)
    (_hrem : rv64_remu bodyLenW strideW = 0)
    (hcap : BitVec.ult capW (rv64_divu bodyLenW strideW)) :
    ¬ fixedListOkW bodyLenW strideW capW := by
  intro h
  have hdiv := rv64_divu_toNat bodyLenW strideW hstride
  have hlt := (ult_iff_lt capW (rv64_divu bodyLenW strideW)).1 hcap
  have hle := h.2
  rw [← hdiv] at hle
  exact Nat.lt_le_asymm hlt hle

/-- Concrete strides match Params guards (named for triple discharge). -/
theorem erh_strides :
    SszType.fixedSize sszDepositRequestType = 192 ∧
    SszType.fixedSize sszWithdrawalRequestType = 76 ∧
    SszType.fixedSize sszConsolidationRequestType = 116 ∧
    SszType.fixedSize sszBuilderDepositRequestType = 184 ∧
    SszType.fixedSize sszBuilderExitRequestType = 68 := by
  decide

theorem erh_caps :
    MAX_DEPOSIT_REQUESTS_PER_PAYLOAD = 8192 ∧
    MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD = 16 ∧
    MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD = 2 ∧
    MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD = 64 ∧
    MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD = 16 := by
  decide

/-- Deposit cap × stride is exactly the declared `erh_blob` capacity argument
    noted on #11578 (overrun absence for `erh_hash_one` copy). -/
theorem deposit_cap_times_stride_eq :
    MAX_DEPOSIT_REQUESTS_PER_PAYLOAD * SszType.fixedSize sszDepositRequestType
      = 8192 * 192 := by
  decide

end EvmAsm.Codegen.ExecutionRequestsHashVal
