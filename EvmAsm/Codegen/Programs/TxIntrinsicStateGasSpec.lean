/-
  Fn.Spec for `tx_intrinsic_state_gas` (54-instr, a4gbr.2).

  Success path (post EIP-2780):
    frame → extract OK → type_dispatch OK → zeros ABI →
    eip8037_tx_state_gas (proven: *out = 0+0) → epilogue
    a0 = 0 ∧ *out = pureIntrinsicStateGasSuccess (= 0)

  Callees still unproven as full Programs for extract (string) and
  type_dispatch (45-instr Program, no Spec yet). Success arms are
  **named hypotheses** (ExtractAssumed / TypeDispatchAssumed), not axioms.
  eip8037_tx_state_gas is fully proven (Eip8037TxStateGasSpec).

  Honest frame: 64B stack in pre/post (restored). Discharge of
  IntrinsicAssumed.success_flat may need a thin adapter that frames
  stackFree outside the array's assumed footprint, or a small extension
  of IntrinsicAssumed to carry sp/frame — tracked with the leaf PR.
-/

import EvmAsm.Codegen.Programs.TxIntrinsicStateGasProg
import EvmAsm.Codegen.Programs.Eip8037TxStateGasSpec
import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayModel
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxIntrinsicStateGasSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel
open EvmAsm.Codegen.Eip8037TxStateGasSpec
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch)

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure)

abbrev T : Word := BitVec.ofNat 64 GuestAddrs.tx_intrinsic_state_gas
abbrev tisProg : Program := txIntrinsicStateGas_prog
abbrev tisCode : CodeReq := CodeReq.ofProg T tisProg

theorem tis_length : tisProg.length = 54 := by decide

/-- type_dispatch leaf CodeReq (for Assumed discharge under fullCode). -/
abbrev typeProg : Program := txTypeDispatch_prog
abbrev typeCode : CodeReq :=
  CodeReq.ofProg (BitVec.ofNat 64 GuestAddrs.tx_type_dispatch) typeProg

theorem type_length' : typeProg.length = 45 := by decide

/-- Full linked code: intrinsic + ets + type_dispatch. -/
def fullCode : CodeReq := (tisCode.union etsCode).union typeCode

theorem tis_bound : 4 * tisProg.length < 2 ^ 64 := by
  simp only [tis_length]; decide

theorem ets_length' : etsProg.length = 4 := ets_length

/-- Adjacent: ets then tis. -/
theorem tis_ets_disjoint : tisCode.Disjoint etsCode := by
  unfold tisCode etsCode T P
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [tis_length]; decide
  · rw [ets_length']; decide
  · rw [tis_length, ets_length']; decide

private theorem type_tis_disjoint : typeCode.Disjoint tisCode := by
  unfold typeCode tisCode T
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [type_length']; decide
  · rw [tis_length]; decide
  · rw [type_length', tis_length]; decide

private theorem type_ets_disjoint : typeCode.Disjoint etsCode := by
  unfold typeCode etsCode P
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [type_length']; decide
  · rw [ets_length']; decide
  · rw [type_length', ets_length']; decide

theorem tis_ets_type_disjoint : (tisCode.union etsCode).Disjoint typeCode := by
  exact CodeReq.Disjoint.union_left type_tis_disjoint.symm type_ets_disjoint.symm

theorem ets_mono :
    ∀ a i, etsCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  have h := CodeReq.mono_union_right tis_ets_disjoint (fun _ _ h => h) a i hi
  exact CodeReq.union_mono_left a i h

theorem tis_mono :
    ∀ a i, tisCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  have h := CodeReq.union_mono_left (cr1 := tisCode) (cr2 := etsCode) a i hi
  exact CodeReq.union_mono_left a i h

theorem type_mono :
    ∀ a i, typeCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.mono_union_right tis_ets_type_disjoint (fun _ _ h => h) a i hi

/-- 8-slot frame: ra, s0–s6 (x8,x9,x18–x22). -/
def tisFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16),
   (.x18, 24), (.x19, 32), (.x20, 40), (.x21, 48), (.x22, 56)]

theorem tisFrame_length : tisFrame.length = 8 := by decide

structure TisSaved where
  ra : Word
  s0 : Word
  s1 : Word
  s2 : Word
  s3 : Word
  s4 : Word
  s5 : Word
  s6 : Word

def tisSavedVals (s : TisSaved) : Reg → Word
  | .x1  => s.ra
  | .x8  => s.s0
  | .x9  => s.s1
  | .x18 => s.s2
  | .x19 => s.s3
  | .x20 => s.s4
  | .x21 => s.s5
  | .x22 => s.s6
  | _ => 0

/-- Step budgets (over-approx; mono). -/
def nExtractSteps : Nat := 512
def nTypeSteps : Nat := 128
def nTisSuccessSteps : Nat := 64 + nExtractSteps + nTypeSteps + 16

/-- Assumed success contract for `tx_extract_to_address` (still asm string).

    ABI: a0=txBase, a1=len, a2=to_buf, a3=is_creation_out → a0=0 on success.
    RO tx blob ambient; scratch out-cells owned (side effects unconstrained). -/
structure ExtractAssumed (cr : CodeReq) where
  entry : Word
  success_flat :
    ∀ (ret txBase lenW toBuf isCreationPtr : Word)
      (txBytes : List (BitVec 8)),
      (ret &&& ~~~(1 : Word)) = ret →
      lenW = BitVec.ofNat 64 txBytes.length →
      cpsTripleWithin nExtractSteps entry ret cr
        ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ lenW) **
          (.x12 ↦ᵣ toBuf) ** (.x13 ↦ᵣ isCreationPtr) **
          bytesRegion txBase txBytes **
          memOwn toBuf ** memOwn isCreationPtr **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)))
        ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ (0 : Word)) **
          bytesRegion txBase txBytes **
          memOwn toBuf ** memOwn isCreationPtr **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)))

/-- Assumed success contract for `tx_type_dispatch` (45-instr Program).

    ABI: a0=txBase, a1=len, a2=type_out, a3=inner_off_out → a0=0 on success.
    Success-domain only: requires classification status = 0
    (`teerTxTypeDispatch txBytes`).1 = 0 — empty/unknown return a0=1. -/
structure TypeDispatchAssumed (cr : CodeReq) where
  entry : Word
  success_flat :
    ∀ (ret txBase lenW typePtr innerPtr : Word)
      (txBytes : List (BitVec 8)),
      (ret &&& ~~~(1 : Word)) = ret →
      lenW = BitVec.ofNat 64 txBytes.length →
      (teerTxTypeDispatch txBytes).1 = (0 : Word) →
      txBase.toNat % 8 = 0 →
      txBase.toNat + txBytes.length < 2 ^ 64 →
      isValidByteAccess (txBase + BitVec.ofNat 64 0) = true →
      cpsTripleWithin nTypeSteps entry ret cr
        ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ lenW) **
          (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
          bytesRegion txBase txBytes **
          memOwn typePtr ** memOwn innerPtr **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)))
        ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ (0 : Word)) **
          bytesRegion txBase txBytes **
          memOwn typePtr ** memOwn innerPtr **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)))

/-- Combined leaf hypotheses for the intrinsic success path. -/
structure TisCalleeAssumptions (cr : CodeReq) where
  extract : ExtractAssumed cr
  typeDispatch : TypeDispatchAssumed cr

/-- Pure pin: success *out = 0. -/
theorem pure_out_eq :
    pureIntrinsicStateGasSuccess = 0 := rfl

/-- Re-export proven ets leaf under fullCode mono (for callWithin). -/
theorem ets_zero_out_full
    (raIn outPtr oldOut a2v a3v a4v t0Old : Word)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn) :
    cpsTripleWithin 4 P raIn fullCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ a2v) ** (.x13 ↦ᵣ a3v) ** (.x14 ↦ᵣ a4v) **
        (.x15 ↦ᵣ outPtr) ** (.x5 ↦ᵣ t0Old) **
        (outPtr ↦ₘ oldOut) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ a2v) ** (.x13 ↦ᵣ a3v) ** (.x14 ↦ᵣ a4v) **
        (.x15 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (0 : Word)) **
        (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have h := eip8037TxStateGas_zero_out_spec_within raIn outPtr oldOut a2v a3v a4v t0Old hret
  exact cpsTripleWithin_extend_code ets_mono h

#print axioms ets_zero_out_full

end EvmAsm.Codegen.TxIntrinsicStateGasSpec
