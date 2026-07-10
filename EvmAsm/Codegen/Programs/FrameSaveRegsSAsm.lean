/- Byte-identical linked-PC verification of `frame_save_regs`. -/

import EvmAsm.Codegen.Programs.CallFrameSwitch
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Codegen
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
namespace FrameSaveRegsSAsm

#guard GuestAddrs.frame_save_regs = 0x80038968
#guard GuestAddrs.frame_save_area = 0xbc4c9a30

def frameSaveRegsBody : List Instr := frameSaveRegs_prog.dropLast

theorem frameSaveRegs_byte_tie :
    frameSaveRegsBody ++ [.JALR .x0 .x1 (0 : BitVec 12)] = frameSaveRegs_prog := by rfl

def frameSaveRegsCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.frame_save_regs : Word) frameSaveRegs_prog

/-- Save `pcVal` and `codeBase` in the two dwords at
    `frame_save_area + depth * 16`, preserving exact RV64 address arithmetic. -/
theorem frameSaveRegs_spec (depth pcVal codeBase old5 old6 oldPc oldCode ret : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    let ofs := depth <<< 4
    let slot := (GuestAddrs.frame_save_area : Word) + ofs
    cpsTripleWithin 7 (GuestAddrs.frame_save_regs : Word) ret frameSaveRegsCr
      (((.x5 : Reg) ↦ᵣ old5) ** ((.x6 : Reg) ↦ᵣ old6) **
        ((.x10 : Reg) ↦ᵣ depth) ** ((.x11 : Reg) ↦ᵣ pcVal) **
        ((.x12 : Reg) ↦ᵣ codeBase) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((slot + 0) ↦ₘ oldPc) ** ((slot + 8) ↦ₘ oldCode))
      (((.x5 : Reg) ↦ᵣ slot) ** ((.x6 : Reg) ↦ᵣ ofs) **
        ((.x10 : Reg) ↦ᵣ depth) ** ((.x11 : Reg) ↦ᵣ pcVal) **
        ((.x12 : Reg) ↦ᵣ codeBase) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((slot + 0) ↦ₘ pcVal) ** ((slot + 8) ↦ₘ codeBase)) := by
  dsimp only
  let ofs := depth <<< 4
  let slot := (GuestAddrs.frame_save_area : Word) + ofs
  have hla := la_materialize_within .x5 old5
    (GuestAddrs.frame_save_regs : Word) (GuestAddrs.frame_save_area : Word)
    (cr := frameSaveRegsCr) (by decide) (by decide)
    (by unfold frameSaveRegsCr; code_mem) (by unfold frameSaveRegsCr; code_mem)
  rw [show (GuestAddrs.frame_save_regs : Word) + 8 =
      (GuestAddrs.frame_save_regs + 8 : Word) from by decide] at hla
  have hlaF := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ old6) ** ((.x10 : Reg) ↦ᵣ depth) **
      ((.x11 : Reg) ↦ᵣ pcVal) ** ((.x12 : Reg) ↦ᵣ codeBase) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((slot + 0) ↦ₘ oldPc) ** ((slot + 8) ↦ₘ oldCode))
    (by pcf) hla
  have hshift0 := slli_spec_gen_within .x6 .x10 old6 depth (4 : BitVec 6)
    (GuestAddrs.frame_save_regs + 8 : Word) (by decide)
  rw [show (4 : BitVec 6).toNat = 4 from by decide,
    show (GuestAddrs.frame_save_regs + 8 : Word) + 4 =
      (GuestAddrs.frame_save_regs + 12 : Word) from by decide] at hshift0
  have hshift := liftCode (cr' := frameSaveRegsCr) hshift0
    (by unfold frameSaveRegsCr; code_mem)
  have hshiftF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (GuestAddrs.frame_save_area : Word)) **
      ((.x11 : Reg) ↦ᵣ pcVal) ** ((.x12 : Reg) ↦ᵣ codeBase) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((slot + 0) ↦ₘ oldPc) ** ((slot + 8) ↦ₘ oldCode))
    (by pcf) hshift
  have hadd0 := add_spec_gen_rd_eq_rs1_within .x5 .x6
    (GuestAddrs.frame_save_area : Word) ofs
    (GuestAddrs.frame_save_regs + 12 : Word) (by decide)
  rw [show (GuestAddrs.frame_save_regs + 12 : Word) + 4 =
      (GuestAddrs.frame_save_regs + 16 : Word) from by decide] at hadd0
  have hadd := liftCode (cr' := frameSaveRegsCr) hadd0
    (by unfold frameSaveRegsCr; code_mem)
  have haddF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ depth) ** ((.x11 : Reg) ↦ᵣ pcVal) **
      ((.x12 : Reg) ↦ᵣ codeBase) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((slot + 0) ↦ₘ oldPc) ** ((slot + 8) ↦ₘ oldCode)) (by pcf) hadd
  have hsd0 := sd_spec_gen_within .x5 .x11 slot pcVal oldPc 0
    (GuestAddrs.frame_save_regs + 16 : Word)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (GuestAddrs.frame_save_regs + 16 : Word) + 4 =
      (GuestAddrs.frame_save_regs + 20 : Word) from by decide] at hsd0
  have hsd := liftCode (cr' := frameSaveRegsCr) hsd0
    (by unfold frameSaveRegsCr; code_mem)
  have hsdF := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ ofs) ** ((.x10 : Reg) ↦ᵣ depth) **
      ((.x12 : Reg) ↦ᵣ codeBase) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((slot + 8) ↦ₘ oldCode)) (by pcf) hsd
  have hsd8_0 := sd_spec_gen_within .x5 .x12 slot codeBase oldCode 8
    (GuestAddrs.frame_save_regs + 20 : Word)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    show (GuestAddrs.frame_save_regs + 20 : Word) + 4 =
      (GuestAddrs.frame_save_regs + 24 : Word) from by decide] at hsd8_0
  have hsd8 := liftCode (cr' := frameSaveRegsCr) hsd8_0
    (by unfold frameSaveRegsCr; code_mem)
  have hsd8F := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ ofs) ** ((.x10 : Reg) ↦ᵣ depth) **
      ((.x11 : Reg) ↦ᵣ pcVal) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((slot + 0) ↦ₘ pcVal)) (by pcf) hsd8
  have hret0 := EvmAsm.Evm64.ret_spec_within'
    (GuestAddrs.frame_save_regs + 24 : Word) ret
  rw [halign] at hret0
  have hret := liftCode (cr' := frameSaveRegsCr) hret0
    (by unfold frameSaveRegsCr; code_mem)
  have hretF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ slot) ** ((.x6 : Reg) ↦ᵣ ofs) **
      ((.x10 : Reg) ↦ᵣ depth) ** ((.x11 : Reg) ↦ᵣ pcVal) **
      ((.x12 : Reg) ↦ᵣ codeBase) ** ((slot + 0) ↦ₘ pcVal) **
      ((slot + 8) ↦ₘ codeBase)) (by pcf) hret
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaF hshiftF
  have h123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h12 haddF
  have h1234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h123 hsdF
  have h12345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h1234 hsd8F
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h12345 hretF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

#print axioms frameSaveRegs_spec
end FrameSaveRegsSAsm
end EvmAsm.Codegen
