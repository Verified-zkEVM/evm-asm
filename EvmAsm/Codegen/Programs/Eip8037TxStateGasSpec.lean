/-
  Fn.Spec for `eip8037_tx_state_gas` (4-instr leaf, bead a4gbr.2).

  Body:
    t0 = a0 + a1
    *a5 = t0
    a0 = 0
    ret

  a2–a4 ignored (retired v0.5 ABI slots). Used by `tx_intrinsic_state_gas`
  with a0=a1=0 so *out = 0 (= pureIntrinsicStateGasSuccess).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Codegen.Programs.IntrinsicGas
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.Eip8037TxStateGasSpec

open EvmAsm.Rv64
open EvmAsm.Codegen

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

abbrev P : Word := BitVec.ofNat 64 GuestAddrs.eip8037_tx_state_gas
abbrev etsProg : Program := eip8037TxStateGas_prog
abbrev etsCode : CodeReq := CodeReq.ofProg P etsProg

theorem ets_length : etsProg.length = 4 := by decide

private theorem se12_zero : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

private theorem ets_bound : 4 * etsProg.length < 2 ^ 64 := by
  simp only [ets_length]; decide

private theorem P_plus_4 : P + 4 = P + BitVec.ofNat 64 (4 * 1) := by decide
private theorem P_plus_8 : P + 8 = P + BitVec.ofNat 64 (4 * 2) := by decide
private theorem P_plus_12 : P + 12 = P + BitVec.ofNat 64 (4 * 3) := by decide

set_option maxRecDepth 8000 in
/-- Full leaf: `*outPtr = a0 + a1`, return `a0 = 0`. -/
theorem eip8037TxStateGas_spec_within
    (raIn outPtr oldOut a0v a1v a2v a3v a4v t0Old : Word)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn) :
    cpsTripleWithin 4 P raIn etsCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ a2v) ** (.x13 ↦ᵣ a3v) ** (.x14 ↦ᵣ a4v) **
        (.x15 ↦ᵣ outPtr) ** (.x5 ↦ᵣ t0Old) **
        (outPtr ↦ₘ oldOut) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ a2v) ** (.x13 ↦ᵣ a3v) ** (.x14 ↦ᵣ a4v) **
        (.x15 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (a0v + a1v)) **
        (outPtr ↦ₘ (a0v + a1v)) ** (.x0 ↦ᵣ (0 : Word))) := by
  -- [0] ADD x5, x10, x11
  have h0 := add_spec_gen_within .x5 .x10 .x11 a0v a1v t0Old P (by decide)
  have h0e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at P P etsProg 0 (.ADD .x5 .x10 .x11)
      (by decide) (by rw [ets_length]; decide) rfl ets_bound) h0
  have h0F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x12 ↦ᵣ a2v) ** (.x13 ↦ᵣ a3v) ** (.x14 ↦ᵣ a4v) **
        (.x15 ↦ᵣ outPtr) ** (outPtr ↦ₘ oldOut) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h0e
  -- [1] SD x15, x5, 0
  have h1 := sd_spec_gen_within .x15 .x5 outPtr (a0v + a1v) oldOut
    (0 : BitVec 12) (P + 4)
  rw [show outPtr + signExtend12 (0 : BitVec 12) = outPtr from by
    rw [se12_zero]; exact BitVec.add_zero outPtr] at h1
  have h1e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at P (P + 4) etsProg 1 (.SD .x15 .x5 (0 : BitVec 12))
      P_plus_4 (by rw [ets_length]; decide) rfl ets_bound) h1
  have h1F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ a2v) ** (.x13 ↦ᵣ a3v) ** (.x14 ↦ᵣ a4v) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h1e
  -- [2] LI x10, 0
  have h2 := li_spec_gen_within .x10 a0v (0 : Word) (P + 8) (by decide)
  have h2e := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at P (P + 8) etsProg 2 (.LI .x10 (0 : Word))
      P_plus_8 (by rw [ets_length]; decide) rfl ets_bound) h2
  have h2F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ a1v) ** (.x12 ↦ᵣ a2v) ** (.x13 ↦ᵣ a3v) **
        (.x14 ↦ᵣ a4v) ** (.x15 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (a0v + a1v)) **
        (outPtr ↦ₘ (a0v + a1v)) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h2e
  -- [3] JALR x0, x1, 0
  have hexit : ((raIn + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) = raIn := by
    have hz : raIn + signExtend12 (0 : BitVec 12) = raIn := by
      rw [se12_zero]; exact BitVec.add_zero raIn
    rw [hz, hret]
  have h3 : cpsTripleWithin 1 (P + 12) raIn etsCode
      (.x1 ↦ᵣ raIn) (.x1 ↦ᵣ raIn) := by
    have h0 := jalr_x0_spec_gen_within .x1 raIn (0 : BitVec 12) (P + 12)
    rw [hexit] at h0
    exact cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at P (P + 12) etsProg 3 (.JALR .x0 .x1 (0 : BitVec 12))
        P_plus_12 (by rw [ets_length]; decide) rfl ets_bound) h0
  -- Frame ordered to match h2F post after xperm: x10 ** x1 ** rest
  have h3F :=
    cpsTripleWithin_frameR
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ a1v) ** (.x12 ↦ᵣ a2v) **
        (.x13 ↦ᵣ a3v) ** (.x14 ↦ᵣ a4v) ** (.x15 ↦ᵣ outPtr) **
        (.x5 ↦ᵣ (a0v + a1v)) ** (outPtr ↦ₘ (a0v + a1v)) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) h3
  have c01 :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have c02 :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 h2F
  have c03 :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 h3F
  -- Reshape framed pre to theorem pre (xperm); post already matches.
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) c03

set_option maxRecDepth 8000 in
/-- Specialization: a0=a1=0 → *out=0 (tx_intrinsic success path). -/
theorem eip8037TxStateGas_zero_out_spec_within
    (raIn outPtr oldOut a2v a3v a4v t0Old : Word)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn) :
    cpsTripleWithin 4 P raIn etsCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ a2v) ** (.x13 ↦ᵣ a3v) ** (.x14 ↦ᵣ a4v) **
        (.x15 ↦ᵣ outPtr) ** (.x5 ↦ᵣ t0Old) **
        (outPtr ↦ₘ oldOut) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ a2v) ** (.x13 ↦ᵣ a3v) ** (.x14 ↦ᵣ a4v) **
        (.x15 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (0 : Word)) **
        (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have h := eip8037TxStateGas_spec_within raIn outPtr oldOut 0 0 a2v a3v a4v t0Old hret
  simpa only [BitVec.zero_add] using h

#print axioms eip8037TxStateGas_spec_within

end EvmAsm.Codegen.Eip8037TxStateGasSpec
