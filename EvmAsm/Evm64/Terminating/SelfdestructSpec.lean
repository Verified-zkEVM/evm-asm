/-
  EvmAsm.Evm64.Terminating.SelfdestructSpec

  Halt-triple spec for the `SELFDESTRUCT` (0xff) handler's halt tail — a direct
  clone of `StopSpec` with the routing code `4` in place of `1` (as `InvalidSpec`
  uses `3`).

  `evm_selfdestruct_stack_spec_within` is a `cpsTripleWithin 7` over the verified
  `evm_selfdestruct` program (`SelfdestructProgram.lean`), the byte image of the
  emitted `dispatchHaltRet 4` tail. It proves the flag-set-and-return behavior:
  the `evm_halt_flag` cell goes `f0 → 4`, `x5 := 4`, `x6 := flagAddr`,
  `x1 := resumeAddr`, and control exits at `resume &&& ~~~1`.

  Scope: this proves only the halt/routing tail (like STOP/INVALID). The handler's
  preceding effects body — cold-access gas, EIP-6780 created-in-tx detection,
  balance transfer to the beneficiary, EIP-7708 log — is unverified glue
  (documented in DRIFT); a future phase can prove it via `EL/SelfdestructEffects`.

  The two linker `la`s stay symbolic, carried as reconstruction hypotheses
  `hla2` / `hla1`, exactly as `StopSpec`. Kernel-checkable throughout (classical-3
  only).
-/

import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Rv64.Tactics.XPermPure
import EvmAsm.Evm64.Terminating.SelfdestructProgram

namespace EvmAsm.Evm64.Terminating

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64

/-- **The verified SELFDESTRUCT (0xff) halt tail.** Sitting at `hbase` (the
    emitted `dispatchHaltRet 4` tail entry, after the effects-body glue), the
    seven instructions of `evm_selfdestruct` set the `evm_halt_flag` cell to the
    SELFDESTRUCT routing code `4`, point `x1` at `.dispatch_resume`, and `ret` —
    reaching `resume &&& ~~~1`.  Direct STOP clone with routing code 4. -/
theorem evm_selfdestruct_stack_spec_within (hi2 : BitVec 20) (lo2 : BitVec 12)
    (hi1 : BitVec 20) (lo1 : BitVec 12)
    (hbase flag resume v5 v6 v1 f0 : Word)
    (hla2 : hbase + 4 + ((hi2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo2 = flag)
    (hla1 : hbase + 16 + ((hi1.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo1 = resume) :
    cpsTripleWithin 7 hbase (resume &&& ~~~1)
      (CodeReq.ofProg hbase (evm_selfdestruct hi2 lo2 hi1 lo1))
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x1 ↦ᵣ v1) ** (flag ↦ₘ f0))
      ((.x5 ↦ᵣ (4 : Word)) ** (.x6 ↦ᵣ flag) ** (.x1 ↦ᵣ resume) **
        (flag ↦ₘ (4 : Word))) := by
  -- Step 1: LI x5, 4 at hbase.
  have t1 := li_spec_within .x5 v5 4 hbase (by nofun)
  have t1f := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x1 ↦ᵣ v1) ** (flag ↦ₘ f0)) (by pcFree) t1
  -- Step 2: AUIPC x6, hi2 at hbase+4.
  have t2 := auipc_spec_within .x6 v6 hi2 (hbase + 4) (by nofun)
  rw [show (hbase + 4 : Word) + 4 = hbase + 8 from by bv_omega] at t2
  have t2f := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (4 : Word)) ** (.x1 ↦ᵣ v1) ** (flag ↦ₘ f0)) (by pcFree) t2
  have hd12 : (CodeReq.singleton hbase (Instr.LI .x5 4)).Disjoint
      (CodeReq.singleton (hbase + 4) (Instr.AUIPC .x6 hi2)) :=
    CodeReq.Disjoint.singleton (by bv_omega)
  have c12 := cpsTripleWithin_seq_with_perm hd12 (fun _ hp => by xperm_hyp hp) t1f t2f
  -- Step 3: ADDI x6, x6, lo2 at hbase+8; result is the flag address.
  have t3 := addi_spec_same_within .x6
    ((hbase + 4) + ((hi2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64) lo2 (hbase + 8)
    (by nofun)
  rw [hla2, show (hbase + 8 : Word) + 4 = hbase + 12 from by bv_omega] at t3
  have t3f := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (4 : Word)) ** (.x1 ↦ᵣ v1) ** (flag ↦ₘ f0)) (by pcFree) t3
  have hd123 : ((CodeReq.singleton hbase (Instr.LI .x5 4)).union
      (CodeReq.singleton (hbase + 4) (Instr.AUIPC .x6 hi2))).Disjoint
      (CodeReq.singleton (hbase + 8) (Instr.ADDI .x6 .x6 lo2)) :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega))
  have c13 := cpsTripleWithin_seq hd123 c12 t3f
  -- Step 4: SD x5, 0(x6) at hbase+12; the flag cell becomes 4.
  have t4 := sd_spec_within .x6 .x5 flag (4 : Word) f0 0 (hbase + 12)
  simp only [signExtend12_0] at t4
  rw [show flag + (0 : Word) = flag from by bv_omega,
      show (hbase + 12 : Word) + 4 = hbase + 16 from by bv_omega] at t4
  have t4f := cpsTripleWithin_frameR (.x1 ↦ᵣ v1) pcFree_regIs t4
  have hd1234 : (((CodeReq.singleton hbase (Instr.LI .x5 4)).union
      (CodeReq.singleton (hbase + 4) (Instr.AUIPC .x6 hi2))).union
      (CodeReq.singleton (hbase + 8) (Instr.ADDI .x6 .x6 lo2))).Disjoint
      (CodeReq.singleton (hbase + 12) (Instr.SD .x6 .x5 0)) :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.singleton (by bv_omega))
        (CodeReq.Disjoint.singleton (by bv_omega)))
      (CodeReq.Disjoint.singleton (by bv_omega))
  have c14 := cpsTripleWithin_seq_with_perm hd1234 (fun _ hp => by xperm_hyp hp) c13 t4f
  -- Step 5: AUIPC x1, hi1 at hbase+16 (start of `la x1, .dispatch_resume`).
  have t5 := auipc_spec_within .x1 v1 hi1 (hbase + 16) (by nofun)
  rw [show (hbase + 16 : Word) + 4 = hbase + 20 from by bv_omega] at t5
  have t5f := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ flag) ** (.x5 ↦ᵣ (4 : Word)) ** (flag ↦ₘ (4 : Word))) (by pcFree) t5
  have hd12345 : ((((CodeReq.singleton hbase (Instr.LI .x5 4)).union
      (CodeReq.singleton (hbase + 4) (Instr.AUIPC .x6 hi2))).union
      (CodeReq.singleton (hbase + 8) (Instr.ADDI .x6 .x6 lo2))).union
      (CodeReq.singleton (hbase + 12) (Instr.SD .x6 .x5 0))).Disjoint
      (CodeReq.singleton (hbase + 16) (Instr.AUIPC .x1 hi1)) :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.union_left
          (CodeReq.Disjoint.singleton (by bv_omega))
          (CodeReq.Disjoint.singleton (by bv_omega)))
        (CodeReq.Disjoint.singleton (by bv_omega)))
      (CodeReq.Disjoint.singleton (by bv_omega))
  have c15 := cpsTripleWithin_seq_with_perm hd12345 (fun _ hp => by xperm_hyp hp) c14 t5f
  -- Step 6: ADDI x1, x1, lo1 at hbase+20; result is the resume address.
  have t6 := addi_spec_same_within .x1
    ((hbase + 16) + ((hi1.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64) lo1 (hbase + 20)
    (by nofun)
  rw [hla1, show (hbase + 20 : Word) + 4 = hbase + 24 from by bv_omega] at t6
  have t6f := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ flag) ** (.x5 ↦ᵣ (4 : Word)) ** (flag ↦ₘ (4 : Word))) (by pcFree) t6
  have hd123456 : (((((CodeReq.singleton hbase (Instr.LI .x5 4)).union
      (CodeReq.singleton (hbase + 4) (Instr.AUIPC .x6 hi2))).union
      (CodeReq.singleton (hbase + 8) (Instr.ADDI .x6 .x6 lo2))).union
      (CodeReq.singleton (hbase + 12) (Instr.SD .x6 .x5 0))).union
      (CodeReq.singleton (hbase + 16) (Instr.AUIPC .x1 hi1))).Disjoint
      (CodeReq.singleton (hbase + 20) (Instr.ADDI .x1 .x1 lo1)) :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.union_left
          (CodeReq.Disjoint.union_left
            (CodeReq.Disjoint.singleton (by bv_omega))
            (CodeReq.Disjoint.singleton (by bv_omega)))
          (CodeReq.Disjoint.singleton (by bv_omega)))
        (CodeReq.Disjoint.singleton (by bv_omega)))
      (CodeReq.Disjoint.singleton (by bv_omega))
  have c16 := cpsTripleWithin_seq hd123456 c15 t6f
  -- Step 7: JALR x0, x1, 0 at hbase+24 (ret; reaches resume &&& ~~~1).
  have t7 := ret_spec_within' (hbase + 24) resume
  have t7f := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ flag) ** (.x5 ↦ᵣ (4 : Word)) ** (flag ↦ₘ (4 : Word))) (by pcFree) t7
  have hd1234567 : ((((((CodeReq.singleton hbase (Instr.LI .x5 4)).union
      (CodeReq.singleton (hbase + 4) (Instr.AUIPC .x6 hi2))).union
      (CodeReq.singleton (hbase + 8) (Instr.ADDI .x6 .x6 lo2))).union
      (CodeReq.singleton (hbase + 12) (Instr.SD .x6 .x5 0))).union
      (CodeReq.singleton (hbase + 16) (Instr.AUIPC .x1 hi1))).union
      (CodeReq.singleton (hbase + 20) (Instr.ADDI .x1 .x1 lo1))).Disjoint
      (CodeReq.singleton (hbase + 24) (Instr.JALR .x0 .x1 0)) :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.union_left
          (CodeReq.Disjoint.union_left
            (CodeReq.Disjoint.union_left
              (CodeReq.Disjoint.singleton (by bv_omega))
              (CodeReq.Disjoint.singleton (by bv_omega)))
            (CodeReq.Disjoint.singleton (by bv_omega)))
          (CodeReq.Disjoint.singleton (by bv_omega)))
        (CodeReq.Disjoint.singleton (by bv_omega)))
      (CodeReq.Disjoint.singleton (by bv_omega))
  have c17 := cpsTripleWithin_seq hd1234567 c16 t7f
  -- Align the CodeReq with the ofProg form and the post shape.
  have hcode : CodeReq.ofProg hbase (evm_selfdestruct hi2 lo2 hi1 lo1) =
      ((((((CodeReq.singleton hbase (Instr.LI .x5 4)).union
        (CodeReq.singleton (hbase + 4) (Instr.AUIPC .x6 hi2))).union
        (CodeReq.singleton (hbase + 8) (Instr.ADDI .x6 .x6 lo2))).union
        (CodeReq.singleton (hbase + 12) (Instr.SD .x6 .x5 0))).union
        (CodeReq.singleton (hbase + 16) (Instr.AUIPC .x1 hi1))).union
        (CodeReq.singleton (hbase + 20) (Instr.ADDI .x1 .x1 lo1))).union
        (CodeReq.singleton (hbase + 24) (Instr.JALR .x0 .x1 0)) := by
    simp only [evm_selfdestruct, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
      CodeReq.union_empty_right]
    rw [show (hbase + 4 : Word) + 4 = hbase + 8 from by bv_omega,
        show (hbase + 8 : Word) + 4 = hbase + 12 from by bv_omega,
        show (hbase + 12 : Word) + 4 = hbase + 16 from by bv_omega,
        show (hbase + 16 : Word) + 4 = hbase + 20 from by bv_omega,
        show (hbase + 20 : Word) + 4 = hbase + 24 from by bv_omega]
    simp only [← CodeReq.union_assoc]
  rw [hcode]
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by xperm_hyp hq) c17

end EvmAsm.Evm64.Terminating
