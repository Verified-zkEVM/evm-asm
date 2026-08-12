/-
  EvmAsm.Evm64.Terminating.ReturnHaltSpec

  Halt-triple spec for the *halt core* shared by the `RETURN` (0xf3) and
  `REVERT` (0xfd) handler tails — a direct clone of the `STOP` halt-triple
  (`StopSpec`) and the `INVALID` halt-triple (`InvalidSpec`), differing only in
  the routing code (RETURN/REVERT → `.exit_no_epilogue` = 2, in place of STOP's
  1 / INVALID's 3).

  `evm_return_halt_spec_within` is a `cpsTripleWithin 7` over the verified
  `evm_return_halt` program (`ReturnHaltProgram.lean`), the byte image of the
  emitted `dispatchHaltRet 2` sub-slice. It proves the flag-set-and-return
  behavior:

  * `evm_halt_flag` cell goes from `f0` to `2` (RETURN/REVERT routing code);
  * `x5 := 2`, `x6 := flagAddr` (the halt-flag cell address);
  * `x1 := resumeAddr` (the `.dispatch_resume` address) — the terminating
    tail *rewrites* `x1` via `la x1, resume` before the `ret`, so control
    reaches `resume &&& ~~~1` (the dispatcher's flag-routing resume point)
    rather than the caller's return address;
  * the triple exits at `resume &&& ~~~1`.

  The two linker `la`s (`evm_halt_flag`, `.dispatch_resume`) stay symbolic,
  carried as reconstruction hypotheses `hla2` / `hla1` exactly as the
  guard/glue-track precedents (`GuardedHandlerSpecs.stackGuardHalt`,
  `CalldataLoadGuardedHandlerSpec`) leave theirs; discharging them against the
  emitted ELF is the (deferred) byte-check, shared with the whole family.

  ## Coverage boundary (READ THIS)

  This spec covers ONLY the 7-instruction `dispatchHaltRet 2` halt core, which
  sits at the very END of the emitted `returnRevertTail` (`NoopHalt.lean`).
  It does NOT cover the substantive return-data descriptor window that precedes
  it: the `0xa0010000` header zeroing, the 22-word zeroing loop, the size clamp
  to 176, the `evm_memory[offset..offset+clamped]` copy loop, the first-32-byte
  prefix copy loop, or the size / clamped-size / kind stores. Nor does it cover
  the `preBody` memory-gas glue (with its `.exit_outofgas` branch, TCB per
  decision-1) or the `system_call_mode` capture branch. Proving the full tail
  effect (a `cpsTripleWithin` from the post-gas handler entry through the
  descriptor window to this halt core) is a three-loop-induction,
  TLOAD/CODECOPY-scale effort deferred to a follow-up; until then RETURN /
  REVERT remain `.execSpec` in the registry (they are NOT flipped on the
  strength of this halt core alone).

  Proof method: identical to `StopSpec` / `InvalidSpec` line-for-line, with
  routing code `2` in place of `1` / `3`. Kernel-checkable throughout
  (classical-3 only).
-/

import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Rv64.Tactics.XPermPure
import EvmAsm.Evm64.Terminating.ReturnHaltProgram

namespace EvmAsm.Evm64.Terminating

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64

/-- **The verified RETURN / REVERT (0xf3 / 0xfd) halt core.** Sitting at
    `hbase` (the emitted `dispatchHaltRet 2` sub-slice entry at the end of
    `returnRevertTail`), the seven instructions of `evm_return_halt` set the
    `evm_halt_flag` cell to the RETURN/REVERT routing code `2`, point `x1` at
    `.dispatch_resume`, and `ret` — reaching `resume &&& ~~~1`, the
    dispatcher's flag-routing resume point (`.exit_no_epilogue`).

    `hla2` reconstructs `la x6, evm_halt_flag` (auipc at `hbase + 4`);
    `hla1` reconstructs `la x1, .dispatch_resume` (auipc at `hbase + 16`).
    These tie the symbolic `la` immediate pairs to the linked cell / label
    addresses, exactly as `GuardedHandlerSpecs.stackGuardHalt` leaves `hla2`.

    This is a direct clone of `evm_stop_stack_spec_within` /
    `evm_invalid_stack_spec_within`, differing only in the routing code
    (2 vs 1 / 3). See the module docstring for the coverage boundary: this is
    the shared halt core, NOT the full RETURN/REVERT return-data window. -/
theorem evm_return_halt_spec_within (hi2 : BitVec 20) (lo2 : BitVec 12)
    (hi1 : BitVec 20) (lo1 : BitVec 12)
    (hbase flag resume v5 v6 v1 f0 : Word)
    (hla2 : hbase + 4 + ((hi2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo2 = flag)
    (hla1 : hbase + 16 + ((hi1.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo1 = resume) :
    cpsTripleWithin 7 hbase (resume &&& ~~~1)
      (CodeReq.ofProg hbase (evm_return_halt hi2 lo2 hi1 lo1))
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x1 ↦ᵣ v1) ** (flag ↦ₘ f0))
      ((.x5 ↦ᵣ (2 : Word)) ** (.x6 ↦ᵣ flag) ** (.x1 ↦ᵣ resume) **
        (flag ↦ₘ (2 : Word))) := by
  -- Step 1: LI x5, 2 at hbase.
  have t1 := li_spec_within .x5 v5 2 hbase (by nofun)
  have t1f := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x1 ↦ᵣ v1) ** (flag ↦ₘ f0)) (by pcFree) t1
  -- Step 2: AUIPC x6, hi2 at hbase+4.
  have t2 := auipc_spec_within .x6 v6 hi2 (hbase + 4) (by nofun)
  rw [show (hbase + 4 : Word) + 4 = hbase + 8 from by bv_omega] at t2
  have t2f := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ v1) ** (flag ↦ₘ f0)) (by pcFree) t2
  have hd12 : (CodeReq.singleton hbase (Instr.LI .x5 2)).Disjoint
      (CodeReq.singleton (hbase + 4) (Instr.AUIPC .x6 hi2)) :=
    CodeReq.Disjoint.singleton (by bv_omega)
  have c12 := cpsTripleWithin_seq_with_perm hd12 (fun _ hp => by xperm_hyp hp) t1f t2f
  -- Step 3: ADDI x6, x6, lo2 at hbase+8; result is the flag address.
  have t3 := addi_spec_same_within .x6
    ((hbase + 4) + ((hi2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64) lo2 (hbase + 8)
    (by nofun)
  rw [hla2, show (hbase + 8 : Word) + 4 = hbase + 12 from by bv_omega] at t3
  have t3f := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ v1) ** (flag ↦ₘ f0)) (by pcFree) t3
  have hd123 : ((CodeReq.singleton hbase (Instr.LI .x5 2)).union
      (CodeReq.singleton (hbase + 4) (Instr.AUIPC .x6 hi2))).Disjoint
      (CodeReq.singleton (hbase + 8) (Instr.ADDI .x6 .x6 lo2)) :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega))
  have c13 := cpsTripleWithin_seq hd123 c12 t3f
  -- Step 4: SD x5, 0(x6) at hbase+12; the flag cell becomes 2.
  have t4 := sd_spec_within .x6 .x5 flag (2 : Word) f0 0 (hbase + 12)
  simp only [signExtend12_0] at t4
  rw [show flag + (0 : Word) = flag from by bv_omega,
      show (hbase + 12 : Word) + 4 = hbase + 16 from by bv_omega] at t4
  have t4f := cpsTripleWithin_frameR (.x1 ↦ᵣ v1) pcFree_regIs t4
  have hd1234 : (((CodeReq.singleton hbase (Instr.LI .x5 2)).union
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
    ((.x6 ↦ᵣ flag) ** (.x5 ↦ᵣ (2 : Word)) ** (flag ↦ₘ (2 : Word))) (by pcFree) t5
  have hd12345 : ((((CodeReq.singleton hbase (Instr.LI .x5 2)).union
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
    ((.x6 ↦ᵣ flag) ** (.x5 ↦ᵣ (2 : Word)) ** (flag ↦ₘ (2 : Word))) (by pcFree) t6
  have hd123456 : (((((CodeReq.singleton hbase (Instr.LI .x5 2)).union
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
    ((.x6 ↦ᵣ flag) ** (.x5 ↦ᵣ (2 : Word)) ** (flag ↦ₘ (2 : Word))) (by pcFree) t7
  have hd1234567 : ((((((CodeReq.singleton hbase (Instr.LI .x5 2)).union
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
  have hcode : CodeReq.ofProg hbase (evm_return_halt hi2 lo2 hi1 lo1) =
      ((((((CodeReq.singleton hbase (Instr.LI .x5 2)).union
        (CodeReq.singleton (hbase + 4) (Instr.AUIPC .x6 hi2))).union
        (CodeReq.singleton (hbase + 8) (Instr.ADDI .x6 .x6 lo2))).union
        (CodeReq.singleton (hbase + 12) (Instr.SD .x6 .x5 0))).union
        (CodeReq.singleton (hbase + 16) (Instr.AUIPC .x1 hi1))).union
        (CodeReq.singleton (hbase + 20) (Instr.ADDI .x1 .x1 lo1))).union
        (CodeReq.singleton (hbase + 24) (Instr.JALR .x0 .x1 0)) := by
    simp only [evm_return_halt, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
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
