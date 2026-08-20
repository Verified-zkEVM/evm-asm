/-
  EvmAsm.Codegen.Programs.TxGasResultIncrementsSAsm

  CPS proof for the scalar post-execution gas settlement helper.  The
  implementation is a branch-shaped realization of the EIP-7623/EIP-7778
  formulas; this file keeps the branch facts explicit so the success and
  error exits are both part of one machine theorem.
-/

import EvmAsm.Codegen.Programs.Account
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.RetForwardJoin
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.Tactics.XPermPure

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics

namespace TxGasResultIncrementsSAsm

abbrev T : Word := (GuestAddrs.tx_gas_result_increments : Word)
abbrev CR : CodeReq := CodeReq.ofProg T txGasResultIncrements_prog

def beforeRefund (gasLimit gasLeft : Word) : Word := gasLimit - gasLeft

def refundApplied (gasLimit gasLeft refundCounter : Word) : Word :=
  let before := beforeRefund gasLimit gasLeft
  let quotient := rv64_divu before (5 : Word)
  if BitVec.ult quotient refundCounter then quotient else refundCounter

def afterRefund (gasLimit gasLeft refundCounter : Word) : Word :=
  beforeRefund gasLimit gasLeft - refundApplied gasLimit gasLeft refundCounter

def blockIncrement (gasLimit gasLeft floor : Word) : Word :=
  let before := beforeRefund gasLimit gasLeft
  if BitVec.ult before floor then floor else before

def receiptIncrement (gasLimit gasLeft refundCounter floor : Word) : Word :=
  let after := afterRefund gasLimit gasLeft refundCounter
  if BitVec.ult after floor then floor else after

def txGasResultStatus (gasLimit gasLeft : Word) : Word :=
  if BitVec.ult gasLimit gasLeft then 1 else 0

/--
On the success arm, `refundW` is bounded by `before`: the emitted select takes
the minimum of `refundCounter` and `before / 5`, and unsigned division by five
is at most its dividend.  This is a derived non-wrapping consequence of the
post, not an additional precondition; changing the select source would require
revisiting the subtraction and this contract.
-/
def txGasResultPost (gasLimit gasLeft refundCounter floor : Word)
    (ret : Word) (vf : Reg → Word) : Assertion :=
  if BitVec.ult gasLimit gasLeft then
    ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((.x13 : Reg) ↦ᵣ (0 : Word)) **
      ((.x14 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret) **
      regAtomsOf vf [.x5, .x6, .x7, .x28, .x29, .x30, .x31]
  else
    let before := beforeRefund gasLimit gasLeft
    let quotient := rv64_divu before (5 : Word)
    let refundW := if BitVec.ult quotient refundCounter then quotient else refundCounter
    let after := before - refundW
    let blockW := if BitVec.ult before floor then floor else before
    let receiptW := if BitVec.ult after floor then floor else after
    ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ blockW) **
      ((.x12 : Reg) ↦ᵣ receiptW) ** ((.x13 : Reg) ↦ᵣ before) **
      ((.x14 : Reg) ↦ᵣ refundW) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
      ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundW) **
      ((.x29 : Reg) ↦ᵣ after) ** ((.x30 : Reg) ↦ᵣ blockW) **
      ((.x31 : Reg) ↦ᵣ receiptW)

private def scratch : List Reg := [.x5, .x6, .x7, .x14, .x28, .x29, .x30, .x31]

private theorem scratch_ne_inputs :
    ∀ r ∈ scratch,
      r ≠ (.x10 : Reg) ∧ r ≠ (.x11 : Reg) ∧ r ≠ (.x12 : Reg) ∧
      r ≠ (.x13 : Reg) ∧ r ≠ (.x1 : Reg) := by
  decide

private theorem scratch_reg_atoms (vf : Reg → Word) :
    regAtomsOf vf scratch =
      (((.x5 : Reg) ↦ᵣ vf .x5) ** ((.x6 : Reg) ↦ᵣ vf .x6) **
       ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x14 : Reg) ↦ᵣ vf .x14) **
       ((.x28 : Reg) ↦ᵣ vf .x28) ** ((.x29 : Reg) ↦ᵣ vf .x29) **
       ((.x30 : Reg) ↦ᵣ vf .x30) ** ((.x31 : Reg) ↦ᵣ vf .x31)) := by
  simp only [scratch, regAtomsOf_cons, regAtomsOf_nil, sepConj_emp_right']

private theorem error_tail
    (ret gasLimit gasLeft refundCounter floor : Word)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) (vf : Reg → Word) :
    cpsTripleWithin 6 (T + 80) ret CR
      (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
       ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
       ((.x14 : Reg) ↦ᵣ vf .x14) ** ((.x1 : Reg) ↦ᵣ ret) **
       ((.x5 : Reg) ↦ᵣ vf .x5) ** ((.x6 : Reg) ↦ᵣ vf .x6) **
       ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x28 : Reg) ↦ᵣ vf .x28) **
       ((.x29 : Reg) ↦ᵣ vf .x29) ** ((.x30 : Reg) ↦ᵣ vf .x30) **
       ((.x31 : Reg) ↦ᵣ vf .x31))
      (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
       ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((.x13 : Reg) ↦ᵣ (0 : Word)) **
       ((.x14 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret) **
       ((.x5 : Reg) ↦ᵣ vf .x5) ** ((.x6 : Reg) ↦ᵣ vf .x6) **
       ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x28 : Reg) ↦ᵣ vf .x28) **
       ((.x29 : Reg) ↦ᵣ vf .x29) ** ((.x30 : Reg) ↦ᵣ vf .x30) **
       ((.x31 : Reg) ↦ᵣ vf .x31)) := by
  have h0 := li_spec_gen_within .x10 gasLimit (1 : Word) (T + 80) (by decide)
  have h1 := li_spec_gen_within .x11 gasLeft (0 : Word) (T + 84) (by decide)
  have h2 := li_spec_gen_within .x12 refundCounter (0 : Word) (T + 88) (by decide)
  have h3 := li_spec_gen_within .x13 floor (0 : Word) (T + 92) (by decide)
  have h4 := li_spec_gen_within .x14 (vf .x14) (0 : Word) (T + 96) (by decide)
  have h5 := jalr_x0_spec_gen_within .x1 ret (0 : BitVec 12) (T + 100)
  rw [show T + 80 + 4 = T + 84 from by decide] at h0
  rw [show T + 84 + 4 = T + 88 from by decide] at h1
  rw [show T + 88 + 4 = T + 92 from by decide] at h2
  rw [show T + 92 + 4 = T + 96 from by decide] at h3
  rw [show T + 96 + 4 = T + 100 from by decide] at h4
  have hret : (ret + (0 : Word)) &&& ~~~(1 : Word) = ret := by
    simpa using halignRet
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide, hret] at h5
  have l0 := cpsTripleWithin_extend_code (cr' := CR) (h := h0) (by code_mem)
  have l1 := cpsTripleWithin_extend_code (cr' := CR) (h := h1) (by code_mem)
  have l2 := cpsTripleWithin_extend_code (cr' := CR) (h := h2) (by code_mem)
  have l3 := cpsTripleWithin_extend_code (cr' := CR) (h := h3) (by code_mem)
  have l4 := cpsTripleWithin_extend_code (cr' := CR) (h := h4) (by code_mem)
  have l5 := cpsTripleWithin_extend_code (cr' := CR) (h := h5) (by code_mem)
  runBlock l0 l1 l2 l3 l4 l5

private theorem success_output_tail
    (ret gasLimit gasLeft refundCounter floor v14 before quotient refundW after
      blockW receiptW : Word)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 6 (T + 56) ret CR
      (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
       ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
       ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
       ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
       ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundW) **
       ((.x29 : Reg) ↦ᵣ after) ** ((.x30 : Reg) ↦ᵣ blockW) **
       ((.x31 : Reg) ↦ᵣ receiptW))
      (((.x10 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ blockW) **
       ((.x12 : Reg) ↦ᵣ receiptW) **
       ((.x13 : Reg) ↦ᵣ before) **
       ((.x14 : Reg) ↦ᵣ refundW) ** ((.x1 : Reg) ↦ᵣ ret) **
       ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
       ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundW) **
       ((.x29 : Reg) ↦ᵣ after) **
       ((.x30 : Reg) ↦ᵣ blockW) **
       ((.x31 : Reg) ↦ᵣ receiptW)) := by
  have h0 := li_spec_gen_within .x10 gasLimit (0 : Word) (T + 56) (by decide)
  have h1 := mv_spec_gen_within .x11 .x30 blockW gasLeft (T + 60) (by decide)
  have h2 := mv_spec_gen_within .x12 .x31 receiptW refundCounter (T + 64) (by decide)
  have h3 := mv_spec_gen_within .x13 .x5 before floor (T + 68) (by decide)
  have h4 := mv_spec_gen_within .x14 .x28 refundW v14 (T + 72) (by decide)
  have h5 := jalr_x0_spec_gen_within .x1 ret (0 : BitVec 12) (T + 76)
  rw [show T + 56 + 4 = T + 60 from by decide] at h0
  rw [show T + 60 + 4 = T + 64 from by decide] at h1
  rw [show T + 64 + 4 = T + 68 from by decide] at h2
  rw [show T + 68 + 4 = T + 72 from by decide] at h3
  rw [show T + 72 + 4 = T + 76 from by decide] at h4
  have hret : (ret + (0 : Word)) &&& ~~~(1 : Word) = ret := by
    simpa using halignRet
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide, hret] at h5
  have l0 := cpsTripleWithin_extend_code (cr' := CR) (h := h0) (by code_mem)
  have l1 := cpsTripleWithin_extend_code (cr' := CR) (h := h1) (by code_mem)
  have l2 := cpsTripleWithin_extend_code (cr' := CR) (h := h2) (by code_mem)
  have l3 := cpsTripleWithin_extend_code (cr' := CR) (h := h3) (by code_mem)
  have l4 := cpsTripleWithin_extend_code (cr' := CR) (h := h4) (by code_mem)
  have l5 := cpsTripleWithin_extend_code (cr' := CR) (h := h5) (by code_mem)
  runBlock l0 l1 l2 l3 l4 l5

private theorem success_after_block
    (ret gasLimit gasLeft refundCounter floor v14 before quotient refundW after
      blockW v31 : Word)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 9 (T + 44) ret CR
      (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
       ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
       ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
       ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
       ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundW) **
       ((.x29 : Reg) ↦ᵣ after) ** ((.x30 : Reg) ↦ᵣ blockW) **
       ((.x31 : Reg) ↦ᵣ v31))
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ blockW) **
       ((.x12 : Reg) ↦ᵣ (if BitVec.ult after floor then floor else after)) **
       ((.x13 : Reg) ↦ᵣ before) ** ((.x14 : Reg) ↦ᵣ refundW) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x5 : Reg) ↦ᵣ before) **
       ((.x6 : Reg) ↦ᵣ (5 : Word)) ** ((.x7 : Reg) ↦ᵣ quotient) **
       ((.x28 : Reg) ↦ᵣ refundW) ** ((.x29 : Reg) ↦ᵣ after) **
       ((.x30 : Reg) ↦ᵣ blockW) ** ((.x31 : Reg) ↦ᵣ
         (if BitVec.ult after floor then floor else after))) := by
  have hmv := mv_spec_gen_within .x31 .x29 after v31 (T + 44) (by decide)
  rw [show T + 44 + 4 = T + 48 from by decide] at hmv
  have lmv := cpsTripleWithin_extend_code (cr' := CR) (h := hmv) (by code_mem)
  have hbr := cpsBranchWithin_frameR
    (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
      ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x14 : Reg) ↦ᵣ v14) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x5 : Reg) ↦ᵣ before) **
      ((.x6 : Reg) ↦ᵣ (5 : Word)) ** ((.x7 : Reg) ↦ᵣ quotient) **
      ((.x28 : Reg) ↦ᵣ refundW) ** ((.x29 : Reg) ↦ᵣ after) **
      ((.x30 : Reg) ↦ᵣ blockW))
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := bgeu_spec_gen_within .x31 .x13 (8 : BitVec 13) after floor (T + 48))
      (by code_mem))
  rw [show T + 48 + signExtend13 (8 : BitVec 13) = T + 56 from by decide,
      show T + 48 + 4 = T + 52 from by decide] at hbr
  have hTaken : ¬ BitVec.ult after floor →
      cpsTripleWithin 7 (T + 56) ret CR
        (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
         ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
         ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
         ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
         ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundW) **
         ((.x29 : Reg) ↦ᵣ after) ** ((.x30 : Reg) ↦ᵣ blockW) **
         ((.x31 : Reg) ↦ᵣ after))
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ blockW) **
         ((.x12 : Reg) ↦ᵣ (if BitVec.ult after floor then floor else after)) **
         ((.x13 : Reg) ↦ᵣ before) **
         ((.x14 : Reg) ↦ᵣ refundW) ** ((.x1 : Reg) ↦ᵣ ret) **
         ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
         ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundW) **
         ((.x29 : Reg) ↦ᵣ after) ** ((.x30 : Reg) ↦ᵣ blockW) **
         ((.x31 : Reg) ↦ᵣ (if BitVec.ult after floor then floor else after))) := by
    intro hcond
    have h := success_output_tail ret gasLimit gasLeft refundCounter floor v14
      before quotient refundW after blockW after halignRet
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by
        rw [if_neg hcond]
        xperm_chunked hq)
      (cpsTripleWithin_mono_nSteps (by omega) h)
  have hFall : ¬¬ BitVec.ult after floor →
      cpsTripleWithin 7 (T + 52) ret CR
        (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
         ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
         ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
         ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
         ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundW) **
         ((.x29 : Reg) ↦ᵣ after) ** ((.x30 : Reg) ↦ᵣ blockW) **
         ((.x31 : Reg) ↦ᵣ after))
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ blockW) **
         ((.x12 : Reg) ↦ᵣ (if BitVec.ult after floor then floor else after)) **
         ((.x13 : Reg) ↦ᵣ before) **
         ((.x14 : Reg) ↦ᵣ refundW) ** ((.x1 : Reg) ↦ᵣ ret) **
         ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
         ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundW) **
         ((.x29 : Reg) ↦ᵣ after) ** ((.x30 : Reg) ↦ᵣ blockW) **
         ((.x31 : Reg) ↦ᵣ (if BitVec.ult after floor then floor else after))) := by
    intro hcond
    have hcond' : BitVec.ult after floor := by simpa using hcond
    have hmv2 := mv_spec_gen_within .x31 .x13 floor after (T + 52) (by decide)
    rw [show T + 52 + 4 = T + 56 from by decide] at hmv2
    have lmv2 := cpsTripleWithin_extend_code (cr' := CR) (h := hmv2) (by code_mem)
    have htail := success_output_tail ret gasLimit gasLeft refundCounter floor v14
      before quotient refundW after blockW floor halignRet
    have hmv2F := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
        ((.x12 : Reg) ↦ᵣ refundCounter) **
        ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
        ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundW) **
        ((.x29 : Reg) ↦ᵣ after) ** ((.x30 : Reg) ↦ᵣ blockW)) (by pcf) lmv2
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by rw [if_pos hcond']; xperm_chunked hq)
      (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
        hmv2F htail)
  have hstation := retJoinStation_spec (cond := ¬ BitVec.ult after floor)
    (PT := ((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
      ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
      ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
      ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundW) **
      ((.x29 : Reg) ↦ᵣ after) ** ((.x30 : Reg) ↦ᵣ blockW) **
      ((.x31 : Reg) ↦ᵣ after))
    (PF := ((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
      ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
      ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
      ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundW) **
      ((.x29 : Reg) ↦ᵣ after) ** ((.x30 : Reg) ↦ᵣ blockW) **
      ((.x31 : Reg) ↦ᵣ after))
    hbr
    (fun _ hq => by xperm_hyp hq)
    (fun _ hq => by
      rw [show (¬¬ BitVec.ult after floor) = BitVec.ult after floor from by simp]
      xperm_hyp hq)
    hTaken hFall
  have lmvF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
      ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
      ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
      ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundW) **
      ((.x30 : Reg) ↦ᵣ blockW)) (by pcf) lmv
  have hcomp := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) lmvF hstation
  have hpre : ∀ h,
      (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
       ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
       ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
       ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
       ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundW) **
       ((.x29 : Reg) ↦ᵣ after) ** ((.x30 : Reg) ↦ᵣ blockW) **
       ((.x31 : Reg) ↦ᵣ v31)) h →
      ((((.x29 : Reg) ↦ᵣ after) ** ((.x31 : Reg) ↦ᵣ v31)) **
       ((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
       ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
       ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
       ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
       ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundW) **
       ((.x30 : Reg) ↦ᵣ blockW)) h := by
    intro h hp
    xperm_hyp hp
  exact cpsTripleWithin_weaken hpre (fun _ hq => hq)
    (cpsTripleWithin_mono_nSteps (nSteps := 1 + (1 + 7)) (nSteps' := 9)
      (by decide) hcomp)

private theorem success_after_refund
    (ret gasLimit gasLeft refundCounter floor v14 before quotient refundW after
      v29 v30 v31 : Word)
    (hafter : before - refundW = after)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 13 (T + 28) ret CR
      (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
       ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
       ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
       ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
       ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundW) **
       ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
       ((.x31 : Reg) ↦ᵣ v31))
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (if BitVec.ult before floor then floor else before)) **
       ((.x12 : Reg) ↦ᵣ (if BitVec.ult after floor then floor else after)) ** ((.x13 : Reg) ↦ᵣ before) **
       ((.x14 : Reg) ↦ᵣ refundW) ** ((.x1 : Reg) ↦ᵣ ret) **
       ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
       ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundW) **
       ((.x29 : Reg) ↦ᵣ after) ** ((.x30 : Reg) ↦ᵣ (if BitVec.ult before floor then floor else before)) **
       ((.x31 : Reg) ↦ᵣ (if BitVec.ult after floor then floor else after))) := by
  have hsub := sub_spec_gen_within .x29 .x5 .x28 before refundW v29 (T + 28) (by decide)
  rw [show T + 28 + 4 = T + 32 from by decide] at hsub
  have lsub := cpsTripleWithin_extend_code (cr' := CR) (h := hsub) (by code_mem)
  have hmv := mv_spec_gen_within .x30 .x5 before v30 (T + 32) (by decide)
  rw [show T + 32 + 4 = T + 36 from by decide] at hmv
  have lmv := cpsTripleWithin_extend_code (cr' := CR) (h := hmv) (by code_mem)
  have hbr := cpsBranchWithin_frameR
    (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
      ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x14 : Reg) ↦ᵣ v14) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x5 : Reg) ↦ᵣ before) **
      ((.x6 : Reg) ↦ᵣ (5 : Word)) ** ((.x7 : Reg) ↦ᵣ quotient) **
      ((.x28 : Reg) ↦ᵣ refundW) ** ((.x29 : Reg) ↦ᵣ after) **
      ((.x31 : Reg) ↦ᵣ v31)) (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := bgeu_spec_gen_within .x30 .x13 (8 : BitVec 13) before floor (T + 36))
      (by code_mem))
  rw [show T + 36 + signExtend13 (8 : BitVec 13) = T + 44 from by decide,
      show T + 36 + 4 = T + 40 from by decide] at hbr
  have hTaken : ¬ BitVec.ult before floor →
      cpsTripleWithin 10 (T + 44) ret CR
        (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
         ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
         ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
         ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
         ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundW) **
         ((.x29 : Reg) ↦ᵣ after) ** ((.x30 : Reg) ↦ᵣ before) **
         ((.x31 : Reg) ↦ᵣ v31))
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (if BitVec.ult before floor then floor else before)) **
         ((.x12 : Reg) ↦ᵣ (if BitVec.ult after floor then floor else after)) ** ((.x13 : Reg) ↦ᵣ before) **
         ((.x14 : Reg) ↦ᵣ refundW) ** ((.x1 : Reg) ↦ᵣ ret) **
         ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
         ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundW) **
         ((.x29 : Reg) ↦ᵣ after) ** ((.x30 : Reg) ↦ᵣ (if BitVec.ult before floor then floor else before)) **
         ((.x31 : Reg) ↦ᵣ (if BitVec.ult after floor then floor else after))) := by
    intro hcond
    have h := success_after_block ret gasLimit gasLeft refundCounter floor v14
      before quotient refundW after before v31 halignRet
    have h' := cpsTripleWithin_mono_nSteps (nSteps' := 10) (by decide) h
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by rw [if_neg hcond]; xperm_hyp hq) h'
  have hFall : ¬¬ BitVec.ult before floor →
      cpsTripleWithin 10 (T + 40) ret CR
        (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
         ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
         ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
         ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
         ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundW) **
         ((.x29 : Reg) ↦ᵣ after) ** ((.x30 : Reg) ↦ᵣ before) **
         ((.x31 : Reg) ↦ᵣ v31))
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (if BitVec.ult before floor then floor else before)) **
         ((.x12 : Reg) ↦ᵣ (if BitVec.ult after floor then floor else after)) ** ((.x13 : Reg) ↦ᵣ before) **
         ((.x14 : Reg) ↦ᵣ refundW) ** ((.x1 : Reg) ↦ᵣ ret) **
         ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
         ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundW) **
         ((.x29 : Reg) ↦ᵣ after) ** ((.x30 : Reg) ↦ᵣ (if BitVec.ult before floor then floor else before)) **
         ((.x31 : Reg) ↦ᵣ (if BitVec.ult after floor then floor else after))) := by
    intro hcond
    have hcond' : BitVec.ult before floor := by simpa using hcond
    have hmv2 := mv_spec_gen_within .x30 .x13 floor before (T + 40) (by decide)
    rw [show T + 40 + 4 = T + 44 from by decide] at hmv2
    have lmv2 := cpsTripleWithin_extend_code (cr' := CR) (h := hmv2) (by code_mem)
    have htail := success_after_block ret gasLimit gasLeft refundCounter floor v14
      before quotient refundW after floor v31 halignRet
    have hmv2F := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
        ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x14 : Reg) ↦ᵣ v14) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x5 : Reg) ↦ᵣ before) **
        ((.x6 : Reg) ↦ᵣ (5 : Word)) ** ((.x7 : Reg) ↦ᵣ quotient) **
        ((.x28 : Reg) ↦ᵣ refundW) ** ((.x29 : Reg) ↦ᵣ after) **
        ((.x31 : Reg) ↦ᵣ v31)) (by pcf) lmv2
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by rw [if_pos hcond']; xperm_hyp hq)
      (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
        hmv2F htail)
  have hstation := retJoinStation_spec (cond := ¬ BitVec.ult before floor)
    (PT := ((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
      ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
      ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
      ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundW) **
      ((.x29 : Reg) ↦ᵣ after) ** ((.x30 : Reg) ↦ᵣ before) **
      ((.x31 : Reg) ↦ᵣ v31))
    (PF := ((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
      ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
      ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
      ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundW) **
      ((.x29 : Reg) ↦ᵣ after) ** ((.x30 : Reg) ↦ᵣ before) **
      ((.x31 : Reg) ↦ᵣ v31))
    hbr
    (fun _ hq => by xperm_hyp hq)
    (fun _ hq => by
      rw [show (¬¬ BitVec.ult before floor) = BitVec.ult before floor from by simp]
      xperm_hyp hq)
    hTaken hFall
  have hsubF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
      ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
      ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x6 : Reg) ↦ᵣ (5 : Word)) ** ((.x7 : Reg) ↦ᵣ quotient) **
      ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31)) (by pcf) lsub
  have hmvF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
      ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
      ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x6 : Reg) ↦ᵣ (5 : Word)) ** ((.x7 : Reg) ↦ᵣ quotient) **
      ((.x28 : Reg) ↦ᵣ refundW) ** ((.x29 : Reg) ↦ᵣ after) **
      ((.x31 : Reg) ↦ᵣ v31)) (by pcf) lmv
  have hprefix := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      rw [hafter] at hp
      xperm_chunked hp) hsubF hmvF
  have hfull := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hprefix hstation
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => hq) (cpsTripleWithin_mono_nSteps (nSteps' := 13) (by decide) hfull)

private theorem success_path
    (ret gasLimit gasLeft refundCounter floor v14 before quotient refundW after
      v5 v6 v7 v28 v29 v30 v31 : Word)
    (hbefore : gasLimit - gasLeft = before)
    (hquot : rv64_divu before (5 : Word) = quotient)
    (hrefund : (if BitVec.ult quotient refundCounter then quotient else refundCounter) = refundW)
    (hafter : before - refundW = after)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 19 (T + 4) ret CR
      (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
       ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
       ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
       ((.x7 : Reg) ↦ᵣ v7) ** ((.x28 : Reg) ↦ᵣ v28) **
       ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
       ((.x31 : Reg) ↦ᵣ v31))
      (((.x10 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ (if BitVec.ult before floor then floor else before)) **
       ((.x12 : Reg) ↦ᵣ (if BitVec.ult after floor then floor else after)) **
       ((.x13 : Reg) ↦ᵣ before) ** ((.x14 : Reg) ↦ᵣ refundW) **
       ((.x1 : Reg) ↦ᵣ ret) ** ((.x5 : Reg) ↦ᵣ before) **
       ((.x6 : Reg) ↦ᵣ (5 : Word)) ** ((.x7 : Reg) ↦ᵣ quotient) **
       ((.x28 : Reg) ↦ᵣ refundW) ** ((.x29 : Reg) ↦ᵣ after) **
       ((.x30 : Reg) ↦ᵣ (if BitVec.ult before floor then floor else before)) **
       ((.x31 : Reg) ↦ᵣ (if BitVec.ult after floor then floor else after))) := by
  have hsub := sub_spec_gen_within .x5 .x10 .x11 gasLimit gasLeft v5 (T + 4) (by decide)
  rw [show T + 4 + 4 = T + 8 from by decide] at hsub
  have lsub := cpsTripleWithin_extend_code (cr' := CR) (h := hsub) (by code_mem)
  have hsubF := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
      ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
      ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
      ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31)) (by pcf) lsub
  have hsubF' := cpsTripleWithin_weaken
    (fun _ hp => by
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hp)
    (fun _ hq => by
      rw [hbefore] at hq
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hq) hsubF
  have hli := li_spec_gen_within .x6 v6 (5 : Word) (T + 8) (by decide)
  rw [show T + 8 + 4 = T + 12 from by decide] at hli
  have lli := cpsTripleWithin_extend_code (cr' := CR) (h := hli) (by code_mem)
  have hliF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
      ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
      ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x5 : Reg) ↦ᵣ before) ** ((.x7 : Reg) ↦ᵣ v7) **
      ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
      ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31)) (by pcf) lli
  have hdiv := divu_spec_gen_within .x7 .x5 .x6 v7 before (5 : Word) (T + 12) (by decide)
  rw [show T + 12 + 4 = T + 16 from by decide] at hdiv
  have ldiv := cpsTripleWithin_extend_code (cr' := CR) (h := hdiv) (by code_mem)
  have hdivF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
      ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
      ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x28 : Reg) ↦ᵣ v28) **
      ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
      ((.x31 : Reg) ↦ᵣ v31)) (by pcf) ldiv
  have hmv := mv_spec_gen_within .x28 .x12 refundCounter v28 (T + 16) (by decide)
  rw [show T + 16 + 4 = T + 20 from by decide] at hmv
  have lmv := cpsTripleWithin_extend_code (cr' := CR) (h := hmv) (by code_mem)
  have hmvF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
      ((.x13 : Reg) ↦ᵣ floor) ** ((.x14 : Reg) ↦ᵣ v14) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x5 : Reg) ↦ᵣ before) **
      ((.x6 : Reg) ↦ᵣ (5 : Word)) ** ((.x7 : Reg) ↦ᵣ quotient) **
      ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
      ((.x31 : Reg) ↦ᵣ v31)) (by pcf) lmv
  have hbr := cpsBranchWithin_frameR
    (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
      ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
      ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
      ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
      ((.x31 : Reg) ↦ᵣ v31)) (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := bgeu_spec_gen_within .x7 .x28 (8 : BitVec 13)
        quotient refundCounter (T + 20)) (by code_mem))
  rw [show T + 20 + signExtend13 (8 : BitVec 13) = T + 28 from by decide,
      show T + 20 + 4 = T + 24 from by decide] at hbr
  have hTaken : ¬ BitVec.ult quotient refundCounter →
      cpsTripleWithin 14 (T + 28) ret CR
        (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
         ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
         ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
         ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
         ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundCounter) **
         ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
         ((.x31 : Reg) ↦ᵣ v31))
        (((.x10 : Reg) ↦ᵣ (0 : Word)) **
         ((.x11 : Reg) ↦ᵣ (if BitVec.ult before floor then floor else before)) **
         ((.x12 : Reg) ↦ᵣ (if BitVec.ult after floor then floor else after)) **
         ((.x13 : Reg) ↦ᵣ before) ** ((.x14 : Reg) ↦ᵣ refundW) **
         ((.x1 : Reg) ↦ᵣ ret) ** ((.x5 : Reg) ↦ᵣ before) **
         ((.x6 : Reg) ↦ᵣ (5 : Word)) ** ((.x7 : Reg) ↦ᵣ quotient) **
         ((.x28 : Reg) ↦ᵣ refundW) ** ((.x29 : Reg) ↦ᵣ after) **
         ((.x30 : Reg) ↦ᵣ (if BitVec.ult before floor then floor else before)) **
         ((.x31 : Reg) ↦ᵣ (if BitVec.ult after floor then floor else after))) := by
    intro hcond
    have hrefund' : refundCounter = refundW := by
      rw [if_neg hcond] at hrefund
      exact hrefund
    cases hrefund'
    have hsucc := success_after_refund ret gasLimit gasLeft refundCounter floor v14
      before quotient refundCounter after v29 v30 v31 hafter halignRet
    have hsucc' := cpsTripleWithin_mono_nSteps (nSteps' := 14) (by decide) hsucc
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hp)
      (fun _ hq => by
        simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hq) hsucc'
  have hFall : ¬¬ BitVec.ult quotient refundCounter →
      cpsTripleWithin 14 (T + 24) ret CR
        (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
         ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
         ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
         ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
         ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundCounter) **
         ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
         ((.x31 : Reg) ↦ᵣ v31))
        (((.x10 : Reg) ↦ᵣ (0 : Word)) **
         ((.x11 : Reg) ↦ᵣ (if BitVec.ult before floor then floor else before)) **
         ((.x12 : Reg) ↦ᵣ (if BitVec.ult after floor then floor else after)) **
         ((.x13 : Reg) ↦ᵣ before) ** ((.x14 : Reg) ↦ᵣ refundW) **
         ((.x1 : Reg) ↦ᵣ ret) ** ((.x5 : Reg) ↦ᵣ before) **
         ((.x6 : Reg) ↦ᵣ (5 : Word)) ** ((.x7 : Reg) ↦ᵣ quotient) **
         ((.x28 : Reg) ↦ᵣ refundW) ** ((.x29 : Reg) ↦ᵣ after) **
         ((.x30 : Reg) ↦ᵣ (if BitVec.ult before floor then floor else before)) **
         ((.x31 : Reg) ↦ᵣ (if BitVec.ult after floor then floor else after))) := by
    intro hcond
    have hcond' : BitVec.ult quotient refundCounter := by simpa using hcond
    have hrefund' : quotient = refundW := by
      rw [if_pos hcond'] at hrefund
      exact hrefund
    cases hrefund'
    have hmv2 := mv_spec_gen_within .x28 .x7 quotient refundCounter (T + 24) (by decide)
    rw [show T + 24 + 4 = T + 28 from by decide] at hmv2
    have lmv2 := cpsTripleWithin_extend_code (cr' := CR) (h := hmv2) (by code_mem)
    have hsucc := success_after_refund ret gasLimit gasLeft refundCounter floor v14
      before quotient quotient after v29 v30 v31 hafter halignRet
    have hmv2F := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
        ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
        ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
        ((.x29 : Reg) ↦ᵣ v29) **
        ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31)) (by pcf) lmv2
    have hseq := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hp) hmv2F hsucc
    have hseq' := cpsTripleWithin_mono_nSteps (nSteps' := 14) (by decide) hseq
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hp)
      (fun _ hq => by
        simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hq) hseq'
  have hstation := retJoinStation_spec (cond := ¬ BitVec.ult quotient refundCounter)
    (PT := ((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
      ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
      ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
      ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundCounter) **
      ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
      ((.x31 : Reg) ↦ᵣ v31))
    (PF := ((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
      ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
      ((.x14 : Reg) ↦ᵣ v14) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x5 : Reg) ↦ᵣ before) ** ((.x6 : Reg) ↦ᵣ (5 : Word)) **
      ((.x7 : Reg) ↦ᵣ quotient) ** ((.x28 : Reg) ↦ᵣ refundCounter) **
      ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
      ((.x31 : Reg) ↦ᵣ v31))
    hbr
    (fun _ hq => by
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hq)
    (fun _ hq => by
      rw [show (¬¬ BitVec.ult quotient refundCounter) = BitVec.ult quotient refundCounter from by simp]
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hq)
    hTaken hFall
  have hprefix0 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hp) hsubF' hliF
  have hprefix1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hp) hprefix0 hdivF
  have hprefix2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      rw [hquot] at hp
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hp) hprefix1 hmvF
  have hfull := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hp) hprefix2 hstation
  exact cpsTripleWithin_weaken (fun _ hp => by
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hp)
    (fun _ hq => hq) (cpsTripleWithin_mono_nSteps (nSteps' := 19) (by decide) hfull)

theorem tx_gas_result_increments_spec
    (ret gasLimit gasLeft refundCounter floor : Word)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) (vf : Reg → Word) :
    cpsTripleWithin 20 T ret CR
      (((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
       ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
       ((.x14 : Reg) ↦ᵣ vf .x14) ** ((.x1 : Reg) ↦ᵣ ret) **
       regAtomsOf vf [.x5, .x6, .x7, .x28, .x29, .x30, .x31])
      (txGasResultPost gasLimit gasLeft refundCounter floor ret vf) := by
  have hbr := cpsBranchWithin_frameR
    (((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
      ((.x14 : Reg) ↦ᵣ vf .x14) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x5 : Reg) ↦ᵣ vf .x5) ** ((.x6 : Reg) ↦ᵣ vf .x6) **
      ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x28 : Reg) ↦ᵣ vf .x28) **
      ((.x29 : Reg) ↦ᵣ vf .x29) ** ((.x30 : Reg) ↦ᵣ vf .x30) **
      ((.x31 : Reg) ↦ᵣ vf .x31)) (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := bltu_spec_gen_within .x10 .x11 (80 : BitVec 13)
        gasLimit gasLeft T) (by code_mem))
  rw [show T + signExtend13 (80 : BitVec 13) = T + 80 from by decide] at hbr
  have hstation := retJoinStation_spec (cond := BitVec.ult gasLimit gasLeft)
    (Q := txGasResultPost gasLimit gasLeft refundCounter floor ret vf)
    (PT := ((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
      ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
      ((.x14 : Reg) ↦ᵣ vf .x14) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x5 : Reg) ↦ᵣ vf .x5) ** ((.x6 : Reg) ↦ᵣ vf .x6) **
      ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x28 : Reg) ↦ᵣ vf .x28) **
      ((.x29 : Reg) ↦ᵣ vf .x29) ** ((.x30 : Reg) ↦ᵣ vf .x30) **
      ((.x31 : Reg) ↦ᵣ vf .x31))
    (PF := ((.x10 : Reg) ↦ᵣ gasLimit) ** ((.x11 : Reg) ↦ᵣ gasLeft) **
      ((.x12 : Reg) ↦ᵣ refundCounter) ** ((.x13 : Reg) ↦ᵣ floor) **
      ((.x14 : Reg) ↦ᵣ vf .x14) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x5 : Reg) ↦ᵣ vf .x5) ** ((.x6 : Reg) ↦ᵣ vf .x6) **
      ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x28 : Reg) ↦ᵣ vf .x28) **
      ((.x29 : Reg) ↦ᵣ vf .x29) ** ((.x30 : Reg) ↦ᵣ vf .x30) **
      ((.x31 : Reg) ↦ᵣ vf .x31))
    hbr
    (fun _ hq => by xperm_hyp hq)
    (fun _ hq => by xperm_hyp hq)
    (fun hcond => by
      have herr := error_tail ret gasLimit gasLeft refundCounter floor halignRet vf
      have herr' := cpsTripleWithin_mono_nSteps (nSteps' := 19) (by decide) herr
      exact cpsTripleWithin_weaken
        (fun _ hp => by xperm_chunked hp)
        (fun _ hq => by
          rw [txGasResultPost, if_pos hcond]
          simp only [regAtomsOf_cons, regAtomsOf_nil, sepConj_emp_right']
          xperm_chunked hq) herr')
    (fun hcond => by
      let before := beforeRefund gasLimit gasLeft
      let quotient := rv64_divu before (5 : Word)
      let refundW := if BitVec.ult quotient refundCounter then quotient else refundCounter
      let after := before - refundW
      have hsucc := success_path ret gasLimit gasLeft refundCounter floor (vf .x14)
        before quotient refundW after (vf .x5) (vf .x6) (vf .x7) (vf .x28)
        (vf .x29) (vf .x30) (vf .x31) (by rfl) (by rfl) (by rfl) (by rfl) halignRet
      exact cpsTripleWithin_weaken
        (fun _ hp => by xperm_chunked hp)
        (fun _ hq => by
          rw [txGasResultPost, if_neg hcond]
          simp only [beforeRefund]
          dsimp [before, quotient, refundW, after]
          dsimp [before, beforeRefund, quotient, refundW, after] at hq
          exact hq) hsucc)
  refine cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [regAtomsOf_cons, regAtomsOf_nil, sepConj_emp_right'] at hp ⊢
      xperm_chunked hp)
    (fun _ hq => hq) hstation

#print axioms tx_gas_result_increments_spec

end TxGasResultIncrementsSAsm

end EvmAsm.Codegen
