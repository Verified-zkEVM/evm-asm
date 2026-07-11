/- Byte-identical linked-PC verification of `frame_depth_pop`. -/

import EvmAsm.Codegen.Programs.CallFrameSwitch
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Codegen
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
namespace FrameDepthPopSAsm

def frameDepthPopBody : List Instr :=
  [ .AUIPC .x5 (laHi GuestAddrs.evm_call_depth GuestAddrs.frame_depth_pop),
    .ADDI .x5 .x5 (laLo GuestAddrs.evm_call_depth GuestAddrs.frame_depth_pop),
    .LD .x10 .x5 (0 : BitVec 12), .ADDI .x10 .x10 (-1 : BitVec 12),
    .SD .x5 .x10 (0 : BitVec 12) ]

theorem frameDepthPop_byte_tie :
    frameDepthPopBody ++ [.JALR .x0 .x1 (0 : BitVec 12)] = frameDepthPop_prog := by rfl

def frameDepthPopCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.frame_depth_pop : Word) frameDepthPop_prog

theorem frameDepthPop_spec (depth old5 old10 ret : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 6 (GuestAddrs.frame_depth_pop : Word) ret frameDepthPopCr
      (((.x5 : Reg) ↦ᵣ old5) ** ((.x10 : Reg) ↦ᵣ old10) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((GuestAddrs.evm_call_depth : Word) ↦ₘ depth))
      (((.x5 : Reg) ↦ᵣ (GuestAddrs.evm_call_depth : Word)) **
        ((.x10 : Reg) ↦ᵣ (depth - 1)) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((GuestAddrs.evm_call_depth : Word) ↦ₘ (depth - 1))) := by
  have hla := la_materialize_within .x5 old5
    (GuestAddrs.frame_depth_pop : Word) (GuestAddrs.evm_call_depth : Word)
    (cr := frameDepthPopCr) (by decide) (by decide)
    (by unfold frameDepthPopCr; code_mem) (by unfold frameDepthPopCr; code_mem)
  rw [show (GuestAddrs.frame_depth_pop : Word) + 8 =
      (GuestAddrs.frame_depth_pop + 8 : Word) from by decide] at hla
  have hlaF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ old10) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((GuestAddrs.evm_call_depth : Word) ↦ₘ depth)) (by pcf) hla
  have hld0 := ld_spec_gen_within .x10 .x5
    (GuestAddrs.evm_call_depth : Word) old10 depth 0
    (GuestAddrs.frame_depth_pop + 8 : Word) (by decide)
  rw [show (GuestAddrs.evm_call_depth : Word) + signExtend12 (0 : BitVec 12) =
      (GuestAddrs.evm_call_depth : Word) from by decide,
    show (GuestAddrs.frame_depth_pop + 8 : Word) + 4 =
      (GuestAddrs.frame_depth_pop + 12 : Word) from by decide] at hld0
  have hld := liftCode (cr' := frameDepthPopCr) hld0
    (by unfold frameDepthPopCr; code_mem)
  have hldF := cpsTripleWithin_frameR (((.x1 : Reg) ↦ᵣ ret)) (by pcf) hld
  have hadd0 := addi_spec_gen_same_within .x10 depth (-1 : BitVec 12)
    (GuestAddrs.frame_depth_pop + 12 : Word) (by decide)
  rw [show depth + signExtend12 (-1 : BitVec 12) = depth - 1 from by
      rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      bv_omega,
    show (GuestAddrs.frame_depth_pop + 12 : Word) + 4 =
      (GuestAddrs.frame_depth_pop + 16 : Word) from by decide] at hadd0
  have hadd := liftCode (cr' := frameDepthPopCr) hadd0
    (by unfold frameDepthPopCr; code_mem)
  have haddF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (GuestAddrs.evm_call_depth : Word)) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((GuestAddrs.evm_call_depth : Word) ↦ₘ depth))
    (by pcf) hadd
  have hsd0 := sd_spec_gen_within .x5 .x10
    (GuestAddrs.evm_call_depth : Word) (depth - 1) depth 0
    (GuestAddrs.frame_depth_pop + 16 : Word)
  rw [show (GuestAddrs.evm_call_depth : Word) + signExtend12 (0 : BitVec 12) =
      (GuestAddrs.evm_call_depth : Word) from by decide,
    show (GuestAddrs.frame_depth_pop + 16 : Word) + 4 =
      (GuestAddrs.frame_depth_pop + 20 : Word) from by decide] at hsd0
  have hsd := liftCode (cr' := frameDepthPopCr) hsd0
    (by unfold frameDepthPopCr; code_mem)
  have hsdF := cpsTripleWithin_frameR (((.x1 : Reg) ↦ᵣ ret)) (by pcf) hsd
  have hret0 := EvmAsm.Evm64.ret_spec_within'
    (GuestAddrs.frame_depth_pop + 20 : Word) ret
  rw [halign] at hret0
  have hret := liftCode (cr' := frameDepthPopCr) hret0
    (by unfold frameDepthPopCr; code_mem)
  have hretF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (GuestAddrs.evm_call_depth : Word)) **
      ((.x10 : Reg) ↦ᵣ (depth - 1)) **
      ((GuestAddrs.evm_call_depth : Word) ↦ₘ (depth - 1))) (by pcf) hret
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaF hldF
  have h123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h12 haddF
  have h1234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h123 hsdF
  have h12345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h1234 hretF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h12345

#print axioms frameDepthPop_spec
end FrameDepthPopSAsm
end EvmAsm.Codegen
