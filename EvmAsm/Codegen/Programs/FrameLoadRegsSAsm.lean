/- Byte-identical linked-PC verification of `frame_load_regs`. -/

import EvmAsm.Codegen.Programs.CallFrameSwitch
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Codegen
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
namespace FrameLoadRegsSAsm

#guard GuestAddrs.frame_load_regs = 0x80038984
#guard GuestAddrs.frame_save_area = 0xbc4c9a30

def frameLoadRegsBody : List Instr := frameLoadRegs_prog.dropLast

theorem frameLoadRegs_byte_tie :
    frameLoadRegsBody ++ [.JALR .x0 .x1 (0 : BitVec 12)] = frameLoadRegs_prog := by rfl

def frameLoadRegsCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.frame_load_regs : Word) frameLoadRegs_prog

/-- Load the saved PC and code-base from `frame_save_area + depth * 16` into
    `a0` and `a1`, preserving both global dwords. -/
theorem frameLoadRegs_spec (depth old5 old6 old11 pcVal codeBase ret : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    let ofs := depth <<< 4
    let slot := (GuestAddrs.frame_save_area : Word) + ofs
    cpsTripleWithin 7 (GuestAddrs.frame_load_regs : Word) ret frameLoadRegsCr
      (((.x5 : Reg) ↦ᵣ old5) ** ((.x6 : Reg) ↦ᵣ old6) **
        ((.x10 : Reg) ↦ᵣ depth) ** ((.x11 : Reg) ↦ᵣ old11) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((slot + 0) ↦ₘ pcVal) **
        ((slot + 8) ↦ₘ codeBase))
      (((.x5 : Reg) ↦ᵣ slot) ** ((.x6 : Reg) ↦ᵣ ofs) **
        ((.x10 : Reg) ↦ᵣ pcVal) ** ((.x11 : Reg) ↦ᵣ codeBase) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((slot + 0) ↦ₘ pcVal) **
        ((slot + 8) ↦ₘ codeBase)) := by
  dsimp only
  let ofs := depth <<< 4
  let slot := (GuestAddrs.frame_save_area : Word) + ofs
  have hla := la_materialize_within .x5 old5
    (GuestAddrs.frame_load_regs : Word) (GuestAddrs.frame_save_area : Word)
    (cr := frameLoadRegsCr) (by decide) (by decide)
    (by unfold frameLoadRegsCr; code_mem) (by unfold frameLoadRegsCr; code_mem)
  rw [show (GuestAddrs.frame_load_regs : Word) + 8 =
      (GuestAddrs.frame_load_regs + 8 : Word) from by decide] at hla
  have hlaF := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ old6) ** ((.x10 : Reg) ↦ᵣ depth) **
      ((.x11 : Reg) ↦ᵣ old11) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((slot + 0) ↦ₘ pcVal) ** ((slot + 8) ↦ₘ codeBase)) (by pcf) hla
  have hshift0 := slli_spec_gen_within .x6 .x10 old6 depth (4 : BitVec 6)
    (GuestAddrs.frame_load_regs + 8 : Word) (by decide)
  rw [show (4 : BitVec 6).toNat = 4 from by decide,
    show (GuestAddrs.frame_load_regs + 8 : Word) + 4 =
      (GuestAddrs.frame_load_regs + 12 : Word) from by decide] at hshift0
  have hshift := liftCode (cr' := frameLoadRegsCr) hshift0
    (by unfold frameLoadRegsCr; code_mem)
  have hshiftF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (GuestAddrs.frame_save_area : Word)) **
      ((.x11 : Reg) ↦ᵣ old11) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((slot + 0) ↦ₘ pcVal) ** ((slot + 8) ↦ₘ codeBase)) (by pcf) hshift
  have hadd0 := add_spec_gen_rd_eq_rs1_within .x5 .x6
    (GuestAddrs.frame_save_area : Word) ofs
    (GuestAddrs.frame_load_regs + 12 : Word) (by decide)
  rw [show (GuestAddrs.frame_load_regs + 12 : Word) + 4 =
      (GuestAddrs.frame_load_regs + 16 : Word) from by decide] at hadd0
  have hadd := liftCode (cr' := frameLoadRegsCr) hadd0
    (by unfold frameLoadRegsCr; code_mem)
  have haddF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ depth) ** ((.x11 : Reg) ↦ᵣ old11) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((slot + 0) ↦ₘ pcVal) **
      ((slot + 8) ↦ₘ codeBase)) (by pcf) hadd
  have hld0 := ld_spec_gen_within .x10 .x5 slot depth pcVal 0
    (GuestAddrs.frame_load_regs + 16 : Word) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (GuestAddrs.frame_load_regs + 16 : Word) + 4 =
      (GuestAddrs.frame_load_regs + 20 : Word) from by decide] at hld0
  have hld := liftCode (cr' := frameLoadRegsCr) hld0
    (by unfold frameLoadRegsCr; code_mem)
  have hldF := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ ofs) ** ((.x11 : Reg) ↦ᵣ old11) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((slot + 8) ↦ₘ codeBase)) (by pcf) hld
  have hld8_0 := ld_spec_gen_within .x11 .x5 slot old11 codeBase 8
    (GuestAddrs.frame_load_regs + 20 : Word) (by decide)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    show (GuestAddrs.frame_load_regs + 20 : Word) + 4 =
      (GuestAddrs.frame_load_regs + 24 : Word) from by decide] at hld8_0
  have hld8 := liftCode (cr' := frameLoadRegsCr) hld8_0
    (by unfold frameLoadRegsCr; code_mem)
  have hld8F := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ ofs) ** ((.x10 : Reg) ↦ᵣ pcVal) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((slot + 0) ↦ₘ pcVal)) (by pcf) hld8
  have hret0 := EvmAsm.Evm64.ret_spec_within'
    (GuestAddrs.frame_load_regs + 24 : Word) ret
  rw [halign] at hret0
  have hret := liftCode (cr' := frameLoadRegsCr) hret0
    (by unfold frameLoadRegsCr; code_mem)
  have hretF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ slot) ** ((.x6 : Reg) ↦ᵣ ofs) **
      ((.x10 : Reg) ↦ᵣ pcVal) ** ((.x11 : Reg) ↦ᵣ codeBase) **
      ((slot + 0) ↦ₘ pcVal) ** ((slot + 8) ↦ₘ codeBase)) (by pcf) hret
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaF hshiftF
  have h123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h12 haddF
  have h1234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h123 hldF
  have h12345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h1234 hld8F
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h12345 hretF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

#print axioms frameLoadRegs_spec
end FrameLoadRegsSAsm
end EvmAsm.Codegen
