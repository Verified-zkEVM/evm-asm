/-
  EvmAsm.Codegen.Programs.CreateInitcodeSizeValidSAsm

  Verified SAsm/CodeReq port of `create_initcode_size_valid`.
-/

import EvmAsm.Rv64.SAsm.RetForwardJoin
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Codegen.Programs.CreateInitcodeSizeValid

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

namespace CreateInitcodeSizeValidSAsm

/-- The gate's single code map: the emitted 6-instruction program. -/
abbrev cisvCode (base : Word) : CodeReq := CodeReq.ofProg base cisvProgram

#guard cisvProgram.length = 6

theorem cisv_emit_tie :
    createInitcodeSizeValidFunction
      = "create_initcode_size_valid:\n" ++ emitProgram cisvProgram := rfl

/-- `create_initcode_size_valid`: return 1 iff `len > MAX_INITCODE_SIZE`, else 0. -/
theorem cisvJoin_spec (base ret len v5old : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 4 base ret (cisvCode base)
      ((.x10 ↦ᵣ len) ** (.x5 ↦ᵣ v5old) ** (.x0 ↦ᵣ (0 : Word)) **
        ((.x1 : Reg) ↦ᵣ ret))
      ((.x10 ↦ᵣ (if BitVec.ult (65536 : Word) len then (1 : Word) else (0 : Word))) **
        regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret)) := by
  set Ptail : Assertion := regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) with hPtail
  have hPtailF : Ptail.pcFree := by rw [hPtail]; pcf
  have hvalTail := sharedRetTail_spec (cisvCode base) (base + 8) ret .x10
    (0 : Word) len Ptail hPtailF (by decide) halign
    (CodeReq.ofProg_mono_sub base (base + 8) cisvProgram [.LI .x10 (0 : Word)] 2
      (by bv_omega) (by decide) (by decide) (by decide))
    (CodeReq.ofProg_mono_sub base (base + 8 + 4) cisvProgram [.JALR .x0 .x1 0] 3
      (by bv_omega) (by decide) (by decide) (by decide))
  have hinvTail := sharedRetTail_spec (cisvCode base) (base + 16) ret .x10
    (1 : Word) len Ptail hPtailF (by decide) halign
    (CodeReq.ofProg_mono_sub base (base + 16) cisvProgram [.LI .x10 (1 : Word)] 4
      (by bv_omega) (by decide) (by decide) (by decide))
    (CodeReq.ofProg_mono_sub base (base + 16 + 4) cisvProgram [.JALR .x0 .x1 0] 5
      (by bv_omega) (by decide) (by decide) (by decide))
  have hbr := cpsBranchWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret)) (by pcf)
    (cpsBranchWithin_extend_code
      (h := bltu_spec_gen_within .x5 .x10 (12 : BitVec 13) (65536 : Word) len (base + 4))
      (hmono := CodeReq.ofProg_mono_sub base (base + 4) cisvProgram
        [.BLTU .x5 .x10 (12 : BitVec 13)] 1 (by bv_omega) (by decide) (by decide) (by decide)))
  rw [show (base + 4 : Word) + signExtend13 (12 : BitVec 13) = base + 16 from by
        rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega,
      show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hbr
  have hstation : cpsTripleWithin 3 (base + 4) ret (cisvCode base)
      ((.x5 ↦ᵣ (65536 : Word)) ** (.x10 ↦ᵣ len) ** (.x0 ↦ᵣ (0 : Word)) **
        ((.x1 : Reg) ↦ᵣ ret))
      ((.x10 ↦ᵣ (if BitVec.ult (65536 : Word) len then (1 : Word) else (0 : Word))) **
        ((.x1 : Reg) ↦ᵣ ret) ** Ptail) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
      (retJoinStation_spec
        (PT := (.x5 ↦ᵣ (65536 : Word)) ** (.x10 ↦ᵣ len) **
          ((.x1 : Reg) ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)))
        (PF := (.x5 ↦ᵣ (65536 : Word)) ** (.x10 ↦ᵣ len) **
          ((.x1 : Reg) ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)))
        hbr
        (fun h hq => by xperm_hyp hq)
        (fun h hq => by xperm_hyp hq)
        (fun hc => cpsTripleWithin_weaken
          (fun h hp => by
            rw [hPtail]
            have hp2 := sepConj_mono (regIs_to_regOwn .x5 _) (fun _ hh => hh) h hp
            xperm_hyp hp2)
          (fun h hq => by rw [if_pos hc]; rw [hPtail]; xperm_hyp hq)
          hinvTail)
        (fun hc => cpsTripleWithin_weaken
          (fun h hp => by
            rw [hPtail]
            have hp2 := sepConj_mono (regIs_to_regOwn .x5 _) (fun _ hh => hh) h hp
            xperm_hyp hp2)
          (fun h hq => by rw [if_neg hc]; rw [hPtail]; xperm_hyp hq)
          hvalTail))
  have hpro := cpsTripleWithin_extend_code
    (h := li_spec_gen_within .x5 v5old (65536 : Word) base (by decide))
    (hmono := CodeReq.ofProg_mono_sub base base cisvProgram
      [.LI .x5 (65536 : Word)] 0 (by bv_omega) (by decide) (by decide) (by decide))
  have hproF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ len) ** (.x0 ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ ret)) (by pcf) hpro
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hproF hstation
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => ?_) hall
  rw [hPtail] at hq
  xperm_hyp hq

#print axioms cisvJoin_spec

end CreateInitcodeSizeValidSAsm
end EvmAsm.Codegen
