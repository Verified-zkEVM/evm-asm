/- Byte-identical linked-entry verification of `dispatcher_capture_exec_state_gas`. -/

import EvmAsm.Codegen.Programs.DispatcherExecStateGas
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

namespace DispatcherCaptureExecStateGasSAsm

def captureBody : List Instr := dispatcherCaptureExecStateGas_prog.dropLast

theorem capture_byte_tie :
    captureBody ++ [.JALR .x0 .x1 (0 : BitVec 12)] =
      dispatcherCaptureExecStateGas_prog := by
  rfl

def captureCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.dispatcher_capture_exec_state_gas : Word)
    dispatcherCaptureExecStateGas_prog

private theorem add_zero_word (x : Word) : x + (0 : Word) = x := by
  simp

/-- Read the global executed-state-gas counter and store it in the caller's
    transaction-indexed result cell. The source global is preserved. -/
theorem dispatcherCaptureExecStateGas_spec
    (index old5 old6 old7 gas oldDst retAddr : Word)
    (halign : (retAddr &&& ~~~(1 : Word)) = retAddr) :
    let ofs := index <<< 3
    let dst := (GuestAddrs.bvgr_tx_exec_state_gas : Word) + ofs
    cpsTripleWithin 9 (GuestAddrs.dispatcher_capture_exec_state_gas : Word)
      retAddr captureCr
      (((.x5 : Reg) ↦ᵣ old5) ** ((.x6 : Reg) ↦ᵣ old6) **
        ((.x7 : Reg) ↦ᵣ old7) ** ((.x10 : Reg) ↦ᵣ index) **
        ((.x1 : Reg) ↦ᵣ retAddr) **
        ((GuestAddrs.evm_state_gas_used : Word) ↦ₘ gas) ** (dst ↦ₘ oldDst))
      (((.x5 : Reg) ↦ᵣ gas) ** ((.x6 : Reg) ↦ᵣ dst) **
        ((.x7 : Reg) ↦ᵣ ofs) ** ((.x10 : Reg) ↦ᵣ index) **
        ((.x1 : Reg) ↦ᵣ retAddr) **
        ((GuestAddrs.evm_state_gas_used : Word) ↦ₘ gas) ** (dst ↦ₘ gas)) := by
  dsimp only
  let ofs := index <<< 3
  let dst := (GuestAddrs.bvgr_tx_exec_state_gas : Word) + ofs

  have hla5 := la_materialize_within .x5 old5
    (GuestAddrs.dispatcher_capture_exec_state_gas : Word)
    (GuestAddrs.evm_state_gas_used : Word)
    (cr := captureCr) (by decide) (by decide)
    (by unfold captureCr; code_mem) (by unfold captureCr; code_mem)
  rw [show (GuestAddrs.dispatcher_capture_exec_state_gas : Word) + 8 =
      (GuestAddrs.dispatcher_capture_exec_state_gas + 8 : Word) from by decide] at hla5
  have hla5F := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ old6) ** ((.x7 : Reg) ↦ᵣ old7) **
      ((.x10 : Reg) ↦ᵣ index) ** ((.x1 : Reg) ↦ᵣ retAddr) **
      ((GuestAddrs.evm_state_gas_used : Word) ↦ₘ gas) ** (dst ↦ₘ oldDst))
    (by pcf) hla5

  have hld0 := ld_spec_gen_same_within .x5
    (GuestAddrs.evm_state_gas_used : Word)
    gas 0
    (GuestAddrs.dispatcher_capture_exec_state_gas + 8 : Word) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (GuestAddrs.dispatcher_capture_exec_state_gas + 8 : Word) + 4 =
      (GuestAddrs.dispatcher_capture_exec_state_gas + 12 : Word) from by decide] at hld0
  rw [add_zero_word] at hld0
  have hld := liftCode (cr' := captureCr) hld0
    (by unfold captureCr; code_mem)
  have hldF := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ old6) ** ((.x7 : Reg) ↦ᵣ old7) **
      ((.x10 : Reg) ↦ᵣ index) ** ((.x1 : Reg) ↦ᵣ retAddr) **
      (dst ↦ₘ oldDst)) (by pcf) hld

  have hla6 := la_materialize_within .x6 old6
    (GuestAddrs.dispatcher_capture_exec_state_gas + 12 : Word)
    (GuestAddrs.bvgr_tx_exec_state_gas : Word)
    (cr := captureCr) (by decide) (by decide)
    (by unfold captureCr; code_mem) (by unfold captureCr; code_mem)
  rw [show (GuestAddrs.dispatcher_capture_exec_state_gas + 12 : Word) + 8 =
      (GuestAddrs.dispatcher_capture_exec_state_gas + 20 : Word) from by decide] at hla6
  have hla6F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ gas) ** ((.x7 : Reg) ↦ᵣ old7) **
      ((.x10 : Reg) ↦ᵣ index) ** ((.x1 : Reg) ↦ᵣ retAddr) **
      ((GuestAddrs.evm_state_gas_used : Word) ↦ₘ gas) ** (dst ↦ₘ oldDst))
    (by pcf) hla6

  have hshift0 := slli_spec_gen_within .x7 .x10 old7 index (3 : BitVec 6)
    (GuestAddrs.dispatcher_capture_exec_state_gas + 20 : Word) (by decide)
  rw [show (3 : BitVec 6).toNat = 3 from by decide,
    show (GuestAddrs.dispatcher_capture_exec_state_gas + 20 : Word) + 4 =
      (GuestAddrs.dispatcher_capture_exec_state_gas + 24 : Word) from by decide] at hshift0
  have hshift := liftCode (cr' := captureCr) hshift0
    (by unfold captureCr; code_mem)
  have hshiftF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ gas) **
      ((.x6 : Reg) ↦ᵣ (GuestAddrs.bvgr_tx_exec_state_gas : Word)) **
      ((.x1 : Reg) ↦ᵣ retAddr) **
      ((GuestAddrs.evm_state_gas_used : Word) ↦ₘ gas) ** (dst ↦ₘ oldDst))
    (by pcf) hshift

  have hadd0 := add_spec_gen_rd_eq_rs1_within .x6 .x7
    (GuestAddrs.bvgr_tx_exec_state_gas : Word) ofs
    (GuestAddrs.dispatcher_capture_exec_state_gas + 24 : Word) (by decide)
  rw [show (GuestAddrs.dispatcher_capture_exec_state_gas + 24 : Word) + 4 =
      (GuestAddrs.dispatcher_capture_exec_state_gas + 28 : Word) from by decide] at hadd0
  have hadd := liftCode (cr' := captureCr) hadd0
    (by unfold captureCr; code_mem)
  have haddF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ gas) ** ((.x10 : Reg) ↦ᵣ index) **
      ((.x1 : Reg) ↦ᵣ retAddr) **
      ((GuestAddrs.evm_state_gas_used : Word) ↦ₘ gas) ** (dst ↦ₘ oldDst))
    (by pcf) hadd

  have hsd0 := sd_spec_gen_within .x6 .x5 dst gas oldDst 0
    (GuestAddrs.dispatcher_capture_exec_state_gas + 28 : Word)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (GuestAddrs.dispatcher_capture_exec_state_gas + 28 : Word) + 4 =
      (GuestAddrs.dispatcher_capture_exec_state_gas + 32 : Word) from by decide] at hsd0
  rw [add_zero_word] at hsd0
  have hsd := liftCode (cr' := captureCr) hsd0
    (by unfold captureCr; code_mem)
  have hsdF := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ ofs) ** ((.x10 : Reg) ↦ᵣ index) **
      ((.x1 : Reg) ↦ᵣ retAddr) **
      ((GuestAddrs.evm_state_gas_used : Word) ↦ₘ gas)) (by pcf) hsd

  have hret0 := EvmAsm.Evm64.ret_spec_within'
    (GuestAddrs.dispatcher_capture_exec_state_gas + 32 : Word) retAddr
  rw [halign] at hret0
  have hret := liftCode (cr' := captureCr) hret0
    (by unfold captureCr; code_mem)
  have hretF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ gas) ** ((.x6 : Reg) ↦ᵣ dst) **
      ((.x7 : Reg) ↦ᵣ ofs) ** ((.x10 : Reg) ↦ᵣ index) **
      ((GuestAddrs.evm_state_gas_used : Word) ↦ₘ gas) ** (dst ↦ₘ gas))
    (by pcf) hret

  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hla5F hldF
  have h123 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h12 hla6F
  have h1234 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h123 hshiftF
  have h12345 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h1234 haddF
  have h123456 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h12345 hsdF
  have hall := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h123456 hretF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

#print axioms dispatcherCaptureExecStateGas_spec

end DispatcherCaptureExecStateGasSAsm
end EvmAsm.Codegen
