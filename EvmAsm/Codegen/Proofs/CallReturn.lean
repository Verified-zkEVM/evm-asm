/-
  EvmAsm.Codegen.Proofs.CallReturn

  Minimal caller/callee CPS composition example for verdict-glue helper calls.
  The caller performs `JAL x1, +8`, the callee writes a return value to `x10`
  and returns through `x1`; the continuation slot at `base+4` is present in
  the code map but not executed by this triple.
-/

import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- Tiny non-linear call/return program:
    `base`:    call callee at `base+8`
    `base+4`:  caller continuation (not executed by this triple)
    `base+8`:  callee body
    `base+12`: return via `x1` -/
def callReturnDemoProgram (c : Word) : Program :=
  JAL .x1 (8 : BitVec 21) ;;
  NOP ;;
  LI .x10 c ;;
  EvmAsm.Evm64.cc_ret

abbrev callReturnDemoCode (base c : Word) : CodeReq :=
  CodeReq.ofProg base (callReturnDemoProgram c)

/-- A focused call/return CPS composition artifact: caller `JAL` saves
    `base+4` in `x1`, transfers to the callee at `base+8`, the callee writes
    `c` into `x10`, then `RET` exits at the masked return address. -/
theorem callReturnDemo_spec (base x1old x10old c : Word) :
    cpsTripleWithin 3 base ((base + 4) &&& ~~~1) (callReturnDemoCode base c)
      ((.x1 ↦ᵣ x1old) ** (.x10 ↦ᵣ x10old))
      ((.x1 ↦ᵣ (base + 4)) ** (.x10 ↦ᵣ c)) := by
  have hCall0 := cpsTripleWithin_extend_code
    (h := EvmAsm.Evm64.callNear_spec_within (8 : BitVec 21) base x1old)
    (hmono := CodeReq.ofProg_mono_sub base base (callReturnDemoProgram c)
      [.JAL .x1 (8 : BitVec 21)] 0 (by bv_omega)
      (by rfl)
      (by simp [callReturnDemoProgram, EvmAsm.Evm64.cc_ret, seq, JAL, NOP, LI, JALR, single])
      (by simp [callReturnDemoProgram, EvmAsm.Evm64.cc_ret, seq, JAL, NOP, LI, JALR, single]))
  rw [show base + signExtend21 (8 : BitVec 21) = base + 8 by
    have h_sext : signExtend21 (8 : BitVec 21) = (8 : Word) := by decide
    rw [h_sext]] at hCall0
  have hCall :
      cpsTripleWithin 1 base (base + 8) (callReturnDemoCode base c)
        ((.x1 ↦ᵣ x1old) ** (.x10 ↦ᵣ x10old))
        ((.x1 ↦ᵣ (base + 4)) ** (.x10 ↦ᵣ x10old)) :=
    cpsTripleWithin_frameR (.x10 ↦ᵣ x10old) pcFree_regIs hCall0

  have hLi0 := cpsTripleWithin_extend_code
    (h := li_spec_gen_within .x10 x10old c (base + 8) (by nofun))
    (hmono := CodeReq.ofProg_mono_sub base (base + 8) (callReturnDemoProgram c)
      [.LI .x10 c] 2 (by bv_omega)
      (by rfl)
      (by simp [callReturnDemoProgram, EvmAsm.Evm64.cc_ret, seq, JAL, NOP, LI, JALR, single])
      (by simp [callReturnDemoProgram, EvmAsm.Evm64.cc_ret, seq, JAL, NOP, LI, JALR, single]))
  rw [show base + 8 + 4 = base + 12 by bv_omega] at hLi0
  have hLi :
      cpsTripleWithin 1 (base + 8) (base + 12) (callReturnDemoCode base c)
        ((.x1 ↦ᵣ (base + 4)) ** (.x10 ↦ᵣ x10old))
        ((.x1 ↦ᵣ (base + 4)) ** (.x10 ↦ᵣ c)) :=
    cpsTripleWithin_frameL (.x1 ↦ᵣ (base + 4)) pcFree_regIs hLi0

  have hRet0 := cpsTripleWithin_extend_code
    (h := EvmAsm.Evm64.ret_spec_within' (base + 12) (base + 4))
    (hmono := CodeReq.ofProg_mono_sub base (base + 12) (callReturnDemoProgram c)
      [.JALR .x0 .x1 0] 3 (by bv_omega)
      (by rfl)
      (by simp [callReturnDemoProgram, EvmAsm.Evm64.cc_ret, seq, JAL, NOP, LI, JALR, single])
      (by simp [callReturnDemoProgram, EvmAsm.Evm64.cc_ret, seq, JAL, NOP, LI, JALR, single]))
  have hRet :
      cpsTripleWithin 1 (base + 12) ((base + 4) &&& ~~~1) (callReturnDemoCode base c)
        ((.x1 ↦ᵣ (base + 4)) ** (.x10 ↦ᵣ c))
        ((.x1 ↦ᵣ (base + 4)) ** (.x10 ↦ᵣ c)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameL (.x10 ↦ᵣ c) pcFree_regIs hRet0)

  have hLiRet := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hLi hRet
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hCall hLiRet

end EvmAsm.Codegen.Proofs
