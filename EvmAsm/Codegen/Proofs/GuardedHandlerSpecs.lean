/-
  EvmAsm.Codegen.Proofs.GuardedHandlerSpecs

  Raw-triple layer for the stack-underflow guard prologue (bead evm-asm-vgyg9).

  The emitted handler `h_<OP>` (e.g. `h_ADD`) now carries a 10-instruction
  guard prologue in front of the standard clean-ret body. Exact layout
  (verified by objdump; entry = `base`):

  ```
  base+0:  auipc x14, hi1          ; la x14, evm_cur_stack_top (pair 1/2)
  base+4:  addi  x14, x14, lo1     ; (pair 2/2)
  base+8:  ld    x14, 0(x14)       ; x14 := curTop (cell value)
  base+12: addi  x14, x14, -64     ; -(32*wordCount), wordCount=2 for ADD
  base+16: bgeu  x14, x12, +24     ; no-underflow => skip to base+40 (body)
  base+20: li    x5, 7             ; underflow path: routing code
  base+24: auipc x6, hi2           ; la x6, evm_halt_flag (pair 1/2)
  base+28: addi  x6, x6, lo2       ; (pair 2/2)
  base+32: sd    x5, 0(x6)         ; evm_halt_flag := 7
  base+36: jalr  x0, x1, 0         ; ret (x1 preserved — deliberate)
  base+40: <clean-ret body, e.g. evm_add (30 instrs)>
  then     addi x10, x10, 1
  then     jalr x0, x1, 0          ; ret
  ```

  `x1` preservation on the halt path is deliberate: the ∀-ret handle
  contract requires the handler to return to the dispatcher-provided
  return address on every exit (see docs/4ch8f-interp-strategy.md §3,
  the vgyg9 amendment); the dispatcher then inspects `evm_halt_flag`.

  Contents:
  * `stackUnderflowGuardProgram` — the 10-instruction guard, parameterized
    by the two `la` immediate pairs and the negated stack-window offset;
  * `stackGuardBranch` — the first 5 instructions as a `cpsBranchWithin`
    (taken exit = `base + 40` with `⌜¬underflow⌝`, fall exit = `base + 20`
    with `⌜underflow⌝`);
  * `stackGuardHalt` — the 5-instruction halt block as a `cpsTripleWithin`
    exiting at `x1_init &&& ~~~1` with `evm_halt_flag := 7`;
  * `guardedCleanRetHandlerSpec` — reusable template composing guard +
    halt + an arbitrary clean-ret handler spec into one triple whose
    postcondition is conditional on the underflow check;
  * `evmAddGuardedHandlerSpec` — the concrete ADD (0x01) instance.
-/

import EvmAsm.Codegen.Proofs.HandlerSpecs
import EvmAsm.Rv64.Tactics.XPermPure

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

-- ============================================================================
-- 1. The guard Program + guarded handler Program/CodeReq
-- ============================================================================

/-- First half of the guard: load the current stack-top cell into `x14`
    (via `la`+`ld`), subtract the required stack window (`negOff` is the
    negated byte count, e.g. `-64` for a 2-word opcode), and branch over
    the halt block when there is no underflow. -/
def stackGuardCheckProgram (hi1 : BitVec 20) (lo1 negOff : BitVec 12) : Program :=
  [.AUIPC .x14 hi1, .ADDI .x14 .x14 lo1, .LD .x14 .x14 0,
   .ADDI .x14 .x14 negOff, .BGEU .x14 .x12 24]

/-- Second half of the guard: the underflow (halt) path. Writes the
    routing code 7 to `evm_halt_flag` (located via the `hi2`/`lo2`
    `la` pair) and returns to the dispatcher with `x1` preserved. -/
def stackGuardHaltProgram (hi2 : BitVec 20) (lo2 : BitVec 12) : Program :=
  [.LI .x5 7, .AUIPC .x6 hi2, .ADDI .x6 .x6 lo2, .SD .x6 .x5 0, .JALR .x0 .x1 0]

/-- The full 10-instruction stack-underflow guard prologue, exactly as
    emitted (see the layout table in the file header). -/
def stackUnderflowGuardProgram (hi1 : BitVec 20) (lo1 : BitVec 12)
    (hi2 : BitVec 20) (lo2 : BitVec 12) (negOff : BitVec 12) : Program :=
  [.AUIPC .x14 hi1, .ADDI .x14 .x14 lo1, .LD .x14 .x14 0,
   .ADDI .x14 .x14 negOff, .BGEU .x14 .x12 24, .LI .x5 7,
   .AUIPC .x6 hi2, .ADDI .x6 .x6 lo2, .SD .x6 .x5 0, .JALR .x0 .x1 0]

theorem stackUnderflowGuardProgram_split (hi1 : BitVec 20) (lo1 : BitVec 12)
    (hi2 : BitVec 20) (lo2 : BitVec 12) (negOff : BitVec 12) :
    stackUnderflowGuardProgram hi1 lo1 hi2 lo2 negOff =
      stackGuardCheckProgram hi1 lo1 negOff ++ stackGuardHaltProgram hi2 lo2 := rfl

/-- A clean-ret handler with the stack-underflow guard prologue in front. -/
def guardedCleanRetHandlerProgram (hi1 : BitVec 20) (lo1 : BitVec 12)
    (hi2 : BitVec 20) (lo2 : BitVec 12) (negOff : BitVec 12)
    (body : Program) (n : BitVec 12) : Program :=
  stackUnderflowGuardProgram hi1 lo1 hi2 lo2 negOff ;; cleanRetHandlerProgram body n

/-- CodeReq for a guarded clean-ret handler at base address `base`. -/
abbrev guardedCleanRetHandlerCode (base : Word) (hi1 : BitVec 20) (lo1 : BitVec 12)
    (hi2 : BitVec 20) (lo2 : BitVec 12) (negOff : BitVec 12)
    (body : Program) (n : BitVec 12) : CodeReq :=
  CodeReq.ofProg base (guardedCleanRetHandlerProgram hi1 lo1 hi2 lo2 negOff body n)

-- Byte fidelity: guard is exactly 10 instructions; a guarded ADD handler
-- is exactly 42 (10 guard + 30 body + 2 tail).
#guard (stackUnderflowGuardProgram 0 0 0 0 (-64)).length = 10
#guard (guardedCleanRetHandlerProgram 0 0 0 0 (-64) EvmAsm.Evm64.evm_add 1).length = 42

-- ============================================================================
-- 2a. The guard check as a raw branch spec (instructions base .. base+16)
-- ============================================================================

/-- The first 5 guard instructions as a two-exit branch spec.

    Under the `la` reconstruction hypothesis `hla1` (AUIPC+ADDI resolve to
    the `evm_cur_stack_top` cell address), the block loads the stack-top
    value `curTop`, computes `curTop + signExtend12 negOff` into `x14`, and
    branches to `base + 40` (the body) iff there is no underflow
    (`¬ curTop + negOff <u sp`), falling through to `base + 20` (the halt
    block) otherwise. -/
theorem stackGuardBranch (hi1 : BitVec 20) (lo1 negOff : BitVec 12)
    (base cell sp curTop x14_init : Word)
    (hla1 : base + ((hi1.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo1 = cell) :
    cpsBranchWithin 5 base
      (CodeReq.ofProg base (stackGuardCheckProgram hi1 lo1 negOff))
      ((.x14 ↦ᵣ x14_init) ** (.x12 ↦ᵣ sp) ** (cell ↦ₘ curTop))
      (base + 40)
      ((.x14 ↦ᵣ (curTop + signExtend12 negOff)) ** (.x12 ↦ᵣ sp) ** (cell ↦ₘ curTop) **
        ⌜¬BitVec.ult (curTop + signExtend12 negOff) sp⌝)
      (base + 20)
      ((.x14 ↦ᵣ (curTop + signExtend12 negOff)) ** (.x12 ↦ᵣ sp) ** (cell ↦ₘ curTop) **
        ⌜BitVec.ult (curTop + signExtend12 negOff) sp⌝) := by
  -- Step 1: AUIPC x14, hi1 at base.
  have s1 := auipc_spec_within .x14 x14_init hi1 base (by nofun)
  -- Step 2: ADDI x14, x14, lo1 at base+4; result is the cell address.
  have s2 := addi_spec_same_within .x14
    (base + ((hi1.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64) lo1 (base + 4)
    (by nofun)
  rw [hla1, show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at s2
  have hd12 : (CodeReq.singleton base (Instr.AUIPC .x14 hi1)).Disjoint
      (CodeReq.singleton (base + 4) (Instr.ADDI .x14 .x14 lo1)) :=
    CodeReq.Disjoint.singleton (by bv_omega)
  have c12 := cpsTripleWithin_seq hd12 s1 s2
  -- Step 3: LD x14, 0(x14) at base+8; x14 := curTop.
  have s3 := ld_spec_same_within .x14 cell curTop 0 (base + 8) (by nofun)
  simp only [signExtend12_0] at s3
  rw [show cell + (0 : Word) = cell from by bv_omega,
      show (base + 8 : Word) + 4 = base + 12 from by bv_omega] at s3
  have c12f := cpsTripleWithin_frameR (cell ↦ₘ curTop) pcFree_memIs c12
  have hd123 : ((CodeReq.singleton base (Instr.AUIPC .x14 hi1)).union
      (CodeReq.singleton (base + 4) (Instr.ADDI .x14 .x14 lo1))).Disjoint
      (CodeReq.singleton (base + 8) (Instr.LD .x14 .x14 0)) :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega))
  have c13 := cpsTripleWithin_seq hd123 c12f s3
  -- Step 4: ADDI x14, x14, negOff at base+12.
  have s4 := addi_spec_same_within .x14 curTop negOff (base + 12) (by nofun)
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at s4
  have s4f := cpsTripleWithin_frameR (cell ↦ₘ curTop) pcFree_memIs s4
  have hd1234 : (((CodeReq.singleton base (Instr.AUIPC .x14 hi1)).union
      (CodeReq.singleton (base + 4) (Instr.ADDI .x14 .x14 lo1))).union
      (CodeReq.singleton (base + 8) (Instr.LD .x14 .x14 0))).Disjoint
      (CodeReq.singleton (base + 12) (Instr.ADDI .x14 .x14 negOff)) :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.singleton (by bv_omega))
        (CodeReq.Disjoint.singleton (by bv_omega)))
      (CodeReq.Disjoint.singleton (by bv_omega))
  have c14 := cpsTripleWithin_seq hd1234 c13 s4f
  have c14f := cpsTripleWithin_frameR (.x12 ↦ᵣ sp) pcFree_regIs c14
  -- Step 5: BGEU x14, x12, 24 at base+16.
  have s5 := bgeu_spec_gen_within .x14 .x12 24 (curTop + signExtend12 negOff) sp (base + 16)
  have h24 : signExtend13 (24 : BitVec 13) = (24 : Word) := by decide
  rw [h24, show (base + 16 : Word) + 24 = base + 40 from by bv_omega,
      show (base + 16 : Word) + 4 = base + 20 from by bv_omega] at s5
  have s5f := cpsBranchWithin_frameR (cell ↦ₘ curTop) pcFree_memIs s5
  have hd12345 : ((((CodeReq.singleton base (Instr.AUIPC .x14 hi1)).union
      (CodeReq.singleton (base + 4) (Instr.ADDI .x14 .x14 lo1))).union
      (CodeReq.singleton (base + 8) (Instr.LD .x14 .x14 0))).union
      (CodeReq.singleton (base + 12) (Instr.ADDI .x14 .x14 negOff))).Disjoint
      (CodeReq.singleton (base + 16) (Instr.BGEU .x14 .x12 24)) :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.union_left
          (CodeReq.Disjoint.singleton (by bv_omega))
          (CodeReq.Disjoint.singleton (by bv_omega)))
        (CodeReq.Disjoint.singleton (by bv_omega)))
      (CodeReq.Disjoint.singleton (by bv_omega))
  have br := cpsTripleWithin_seq_cpsBranchWithin_with_perm hd12345
    (fun _ hp => by xperm_hyp hp) c14f s5f
  -- Align the CodeReq with the ofProg form and the pre/post shapes.
  have hcode : CodeReq.ofProg base (stackGuardCheckProgram hi1 lo1 negOff) =
      ((((CodeReq.singleton base (Instr.AUIPC .x14 hi1)).union
        (CodeReq.singleton (base + 4) (Instr.ADDI .x14 .x14 lo1))).union
        (CodeReq.singleton (base + 8) (Instr.LD .x14 .x14 0))).union
        (CodeReq.singleton (base + 12) (Instr.ADDI .x14 .x14 negOff))).union
        (CodeReq.singleton (base + 16) (Instr.BGEU .x14 .x12 24)) := by
    simp only [stackGuardCheckProgram, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
      CodeReq.union_empty_right]
    rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega,
        show (base + 8 : Word) + 4 = base + 12 from by bv_omega,
        show (base + 12 : Word) + 4 = base + 16 from by bv_omega]
    simp only [← CodeReq.union_assoc]
  rw [hcode]
  exact cpsBranchWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_pure hq)
    (fun _ hq => by xperm_pure hq)
    br

-- ============================================================================
-- 2b. The halt block as a raw triple (instructions base+20 .. base+36)
-- ============================================================================

/-- The 5-instruction halt block, stated at its own entry address `hbase`
    (= `base + 20` of the full guard). Writes the routing code 7 to the
    halt-flag cell and returns via `JALR x0, x1, 0`; `x1` is preserved
    (deliberate — see file header). -/
theorem stackGuardHalt (hi2 : BitVec 20) (lo2 : BitVec 12)
    (hbase flag v5 v6 x1_init f0 : Word)
    (hla2 : hbase + 4 + ((hi2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo2 = flag) :
    cpsTripleWithin 5 hbase (x1_init &&& ~~~1)
      (CodeReq.ofProg hbase (stackGuardHaltProgram hi2 lo2))
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x1 ↦ᵣ x1_init) ** (flag ↦ₘ f0))
      ((.x5 ↦ᵣ (7 : Word)) ** (.x6 ↦ᵣ flag) ** (.x1 ↦ᵣ x1_init) **
        (flag ↦ₘ (7 : Word))) := by
  -- Step 1: LI x5, 7 at hbase.
  have t1 := li_spec_within .x5 v5 7 hbase (by nofun)
  have t1f := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x1 ↦ᵣ x1_init) ** (flag ↦ₘ f0)) (by pcFree) t1
  -- Step 2: AUIPC x6, hi2 at hbase+4.
  have t2 := auipc_spec_within .x6 v6 hi2 (hbase + 4) (by nofun)
  rw [show (hbase + 4 : Word) + 4 = hbase + 8 from by bv_omega] at t2
  have t2f := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (7 : Word)) ** (.x1 ↦ᵣ x1_init) ** (flag ↦ₘ f0)) (by pcFree) t2
  have hd12 : (CodeReq.singleton hbase (Instr.LI .x5 7)).Disjoint
      (CodeReq.singleton (hbase + 4) (Instr.AUIPC .x6 hi2)) :=
    CodeReq.Disjoint.singleton (by bv_omega)
  have c12 := cpsTripleWithin_seq_with_perm hd12 (fun _ hp => by xperm_hyp hp) t1f t2f
  -- Step 3: ADDI x6, x6, lo2 at hbase+8; result is the flag address.
  have t3 := addi_spec_same_within .x6
    (hbase + 4 + ((hi2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64) lo2 (hbase + 8)
    (by nofun)
  rw [hla2, show (hbase + 8 : Word) + 4 = hbase + 12 from by bv_omega] at t3
  have t3f := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (7 : Word)) ** (.x1 ↦ᵣ x1_init) ** (flag ↦ₘ f0)) (by pcFree) t3
  have hd123 : ((CodeReq.singleton hbase (Instr.LI .x5 7)).union
      (CodeReq.singleton (hbase + 4) (Instr.AUIPC .x6 hi2))).Disjoint
      (CodeReq.singleton (hbase + 8) (Instr.ADDI .x6 .x6 lo2)) :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega))
  have c13 := cpsTripleWithin_seq hd123 c12 t3f
  -- Step 4: SD x5, 0(x6) at hbase+12; the flag cell becomes 7.
  have t4 := sd_spec_within .x6 .x5 flag (7 : Word) f0 0 (hbase + 12)
  simp only [signExtend12_0] at t4
  rw [show flag + (0 : Word) = flag from by bv_omega,
      show (hbase + 12 : Word) + 4 = hbase + 16 from by bv_omega] at t4
  have t4f := cpsTripleWithin_frameR (.x1 ↦ᵣ x1_init) pcFree_regIs t4
  have hd1234 : (((CodeReq.singleton hbase (Instr.LI .x5 7)).union
      (CodeReq.singleton (hbase + 4) (Instr.AUIPC .x6 hi2))).union
      (CodeReq.singleton (hbase + 8) (Instr.ADDI .x6 .x6 lo2))).Disjoint
      (CodeReq.singleton (hbase + 12) (Instr.SD .x6 .x5 0)) :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.singleton (by bv_omega))
        (CodeReq.Disjoint.singleton (by bv_omega)))
      (CodeReq.Disjoint.singleton (by bv_omega))
  have c14 := cpsTripleWithin_seq_with_perm hd1234 (fun _ hp => by xperm_hyp hp) c13 t4f
  -- Step 5: JALR x0, x1, 0 at hbase+16 (ret; x1 preserved).
  have t5 := EvmAsm.Evm64.ret_spec_within' (hbase + 16) x1_init
  have t5f := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ flag) ** (.x5 ↦ᵣ (7 : Word)) ** (flag ↦ₘ (7 : Word))) (by pcFree) t5
  have hd12345 : ((((CodeReq.singleton hbase (Instr.LI .x5 7)).union
      (CodeReq.singleton (hbase + 4) (Instr.AUIPC .x6 hi2))).union
      (CodeReq.singleton (hbase + 8) (Instr.ADDI .x6 .x6 lo2))).union
      (CodeReq.singleton (hbase + 12) (Instr.SD .x6 .x5 0))).Disjoint
      (CodeReq.singleton (hbase + 16) (Instr.JALR .x0 .x1 0)) :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.union_left
          (CodeReq.Disjoint.singleton (by bv_omega))
          (CodeReq.Disjoint.singleton (by bv_omega)))
        (CodeReq.Disjoint.singleton (by bv_omega)))
      (CodeReq.Disjoint.singleton (by bv_omega))
  have c15 := cpsTripleWithin_seq_with_perm hd12345 (fun _ hp => by xperm_hyp hp) c14 t5f
  -- Align the CodeReq with the ofProg form and the post shape.
  have hcode : CodeReq.ofProg hbase (stackGuardHaltProgram hi2 lo2) =
      ((((CodeReq.singleton hbase (Instr.LI .x5 7)).union
        (CodeReq.singleton (hbase + 4) (Instr.AUIPC .x6 hi2))).union
        (CodeReq.singleton (hbase + 8) (Instr.ADDI .x6 .x6 lo2))).union
        (CodeReq.singleton (hbase + 12) (Instr.SD .x6 .x5 0))).union
        (CodeReq.singleton (hbase + 16) (Instr.JALR .x0 .x1 0)) := by
    simp only [stackGuardHaltProgram, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
      CodeReq.union_empty_right]
    rw [show (hbase + 4 : Word) + 4 = hbase + 8 from by bv_omega,
        show (hbase + 8 : Word) + 4 = hbase + 12 from by bv_omega,
        show (hbase + 12 : Word) + 4 = hbase + 16 from by bv_omega]
    simp only [← CodeReq.union_assoc]
  rw [hcode]
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by xperm_hyp hq) c15

-- ============================================================================
-- 3. The guarded handler template
-- ============================================================================

/-- Lift a clean-ret handler spec (at `base + 40`) through the
    stack-underflow guard prologue (at `base`).

    The handler's pre is exposed in the template-canonical shape
    `((x12 ↦ sp) ** (x5 ↦ v5) ** (x6 ↦ v6) ** P') ** (x10 ↦ x10_init) **
    (x1 ↦ x1_init)` — `x12` feeds the BGEU comparison, and `x5`/`x6` are
    clobbered by the halt path, so they must be split out of the otherwise
    opaque handler frame `P'`.

    The conclusion is a single triple from `base` to `x1_init &&& ~~~1`
    (both paths return to the dispatcher) whose post is conditional on the
    underflow check `curTop + signExtend12 negOff <u sp`:
    * underflow: flag cell = 7, `x5 = 7`, `x6 = flag`, everything else
      (operand window `P'`, `x10`, `x1`, `x12`) unchanged from entry;
    * no underflow: the handler's post `Q`, with the flag cell unchanged.
    On both paths `x14` holds the guard's stack-window computation. -/
theorem guardedCleanRetHandlerSpec
    {nBody : Nat} {base cell flag sp : Word} {body : Program} {n : BitVec 12}
    {P' Q : Assertion}
    (hi1 : BitVec 20) (lo1 : BitVec 12) (hi2 : BitVec 20) (lo2 : BitVec 12)
    (negOff : BitVec 12)
    (hn : 5 ≤ nBody)
    (hP'free : P'.pcFree)
    (hBodyLenBound : body.length < 2 ^ 60)
    (hla1 : base + ((hi1.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo1 = cell)
    -- `base + 20 + 4` is the `AUIPC x6` address `base + 24` (offset 24 in the
    -- handler); stated in `+ 20 + 4` form so it feeds `stackGuardHalt`
    -- (`hbase + 4`, `hbase = base + 20`) with no numeral-regroup bridge.
    (hla2 : base + 20 + 4 + ((hi2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo2 = flag)
    (v5 v6 x10_init x1_init x14_init curTop f0 : Word)
    (h_handler : cpsTripleWithin nBody (base + 40) (x1_init &&& ~~~1)
      (cleanRetHandlerCode (base + 40) body n)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** P') **
        (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      Q) :
    cpsTripleWithin (5 + nBody) base (x1_init &&& ~~~1)
      (guardedCleanRetHandlerCode base hi1 lo1 hi2 lo2 negOff body n)
      ((((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** P') **
         (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init)) **
        (.x14 ↦ᵣ x14_init) ** (cell ↦ₘ curTop) ** (flag ↦ₘ f0))
      (if BitVec.ult (curTop + signExtend12 negOff) sp then
        (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (7 : Word)) ** (.x6 ↦ᵣ flag) ** P') **
          (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init)) **
          (.x14 ↦ᵣ (curTop + signExtend12 negOff)) ** (cell ↦ₘ curTop) **
          (flag ↦ₘ (7 : Word))
      else
        Q ** (.x14 ↦ᵣ (curTop + signExtend12 negOff)) ** (cell ↦ₘ curTop) **
          (flag ↦ₘ f0)) := by
  -- Split the full CodeReq into check / halt / clean-ret regions.
  have hsplit : guardedCleanRetHandlerCode base hi1 lo1 hi2 lo2 negOff body n =
      ((CodeReq.ofProg base (stackGuardCheckProgram hi1 lo1 negOff)).union
        (CodeReq.ofProg (base + 20) (stackGuardHaltProgram hi2 lo2))).union
        (CodeReq.ofProg (base + 40) (cleanRetHandlerProgram body n)) := by
    unfold guardedCleanRetHandlerCode guardedCleanRetHandlerProgram
    rw [stackUnderflowGuardProgram_split]
    unfold seq
    have hOuter : CodeReq.ofProg base
          ((stackGuardCheckProgram hi1 lo1 negOff ++ stackGuardHaltProgram hi2 lo2)
            ++ cleanRetHandlerProgram body n) =
        (CodeReq.ofProg base
            (stackGuardCheckProgram hi1 lo1 negOff ++ stackGuardHaltProgram hi2 lo2)).union
          (CodeReq.ofProg (base + BitVec.ofNat 64
              (4 * (stackGuardCheckProgram hi1 lo1 negOff
                ++ stackGuardHaltProgram hi2 lo2).length))
            (cleanRetHandlerProgram body n)) :=
      CodeReq.ofProg_append
    rw [hOuter]
    have hInner : CodeReq.ofProg base
          (stackGuardCheckProgram hi1 lo1 negOff ++ stackGuardHaltProgram hi2 lo2) =
        (CodeReq.ofProg base (stackGuardCheckProgram hi1 lo1 negOff)).union
          (CodeReq.ofProg (base + BitVec.ofNat 64
              (4 * (stackGuardCheckProgram hi1 lo1 negOff).length))
            (stackGuardHaltProgram hi2 lo2)) :=
      CodeReq.ofProg_append
    rw [hInner,
      show (stackGuardCheckProgram hi1 lo1 negOff
          ++ stackGuardHaltProgram hi2 lo2).length = 10 from rfl,
      show (stackGuardCheckProgram hi1 lo1 negOff).length = 5 from rfl,
      show base + BitVec.ofNat 64 (4 * 10) = base + 40 from by bv_omega,
      show base + BitVec.ofNat 64 (4 * 5) = base + 20 from by bv_omega]
  -- Region disjointness.
  have hd1 : (CodeReq.ofProg base (stackGuardCheckProgram hi1 lo1 negOff)).Disjoint
      (CodeReq.ofProg (base + 20) (stackGuardHaltProgram hi2 lo2)) := by
    intro a
    by_cases hmem : ∃ k : Nat, k < 5 ∧ a = base + BitVec.ofNat 64 (4 * k)
    · right
      obtain ⟨k, hk, ha⟩ := hmem
      apply CodeReq.ofProg_none_range
      intro j hj
      have hj5 : j < 5 := hj
      subst ha
      bv_omega
    · left
      apply CodeReq.ofProg_none_range
      intro k hk heq
      exact hmem ⟨k, hk, heq⟩
  have hd2 : ((CodeReq.ofProg base (stackGuardCheckProgram hi1 lo1 negOff)).union
      (CodeReq.ofProg (base + 20) (stackGuardHaltProgram hi2 lo2))).Disjoint
      (CodeReq.ofProg (base + 40) (cleanRetHandlerProgram body n)) := by
    intro a
    by_cases hmem : ∃ k : Nat, k < 10 ∧ a = base + BitVec.ofNat 64 (4 * k)
    · right
      obtain ⟨k, hk, ha⟩ := hmem
      apply CodeReq.ofProg_none_range
      intro j hj
      rw [cleanRetHandlerProgram_length] at hj
      subst ha
      bv_omega
    · left
      have h1 : CodeReq.ofProg base (stackGuardCheckProgram hi1 lo1 negOff) a = none := by
        apply CodeReq.ofProg_none_range
        intro k hk heq
        have hk5 : k < 5 := hk
        exact hmem ⟨k, by omega, heq⟩
      have h2 : CodeReq.ofProg (base + 20) (stackGuardHaltProgram hi2 lo2) a = none := by
        apply CodeReq.ofProg_none_range
        intro j hj heq
        have hj5 : j < 5 := hj
        exact hmem ⟨5 + j, by omega, by rw [heq]; bv_omega⟩
      rw [CodeReq.union_none_left h1]
      exact h2
  -- Subsumption of each region into the full CodeReq.
  have hsub1 : ∀ a i,
      CodeReq.ofProg base (stackGuardCheckProgram hi1 lo1 negOff) a = some i →
      guardedCleanRetHandlerCode base hi1 lo1 hi2 lo2 negOff body n a = some i := by
    intro a i h
    rw [hsplit]
    exact CodeReq.union_mono_left a i (CodeReq.union_mono_left a i h)
  have hsub2 : ∀ a i,
      CodeReq.ofProg (base + 20) (stackGuardHaltProgram hi2 lo2) a = some i →
      guardedCleanRetHandlerCode base hi1 lo1 hi2 lo2 negOff body n a = some i := by
    intro a i h
    rw [hsplit]
    apply CodeReq.union_mono_left
    rcases hd1 a with h1 | h1
    · rw [CodeReq.union_none_left h1]; exact h
    · rw [h1] at h; cases h
  have hsub3 : ∀ a i,
      CodeReq.ofProg (base + 40) (cleanRetHandlerProgram body n) a = some i →
      guardedCleanRetHandlerCode base hi1 lo1 hi2 lo2 negOff body n a = some i := by
    intro a i h
    rw [hsplit]
    rcases hd2 a with h1 | h1
    · rw [CodeReq.union_none_left h1]; exact h
    · rw [h1] at h; cases h
  -- The guard branch, framed with everything the check does not touch.
  have hbr := stackGuardBranch hi1 lo1 negOff base cell sp curTop x14_init hla1
  have hFbr : ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** P' ** (.x10 ↦ᵣ x10_init) **
      (.x1 ↦ᵣ x1_init) ** (flag ↦ₘ f0) : Assertion).pcFree := by
    repeat first
      | apply pcFree_sepConj
      | exact hP'free
      | exact pcFree_regIs
      | exact pcFree_memIs
  have hbr2 := cpsBranchWithin_extend_code hsub1
    (cpsBranchWithin_frameR
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** P' ** (.x10 ↦ᵣ x10_init) **
        (.x1 ↦ᵣ x1_init) ** (flag ↦ₘ f0))
      hFbr hbr)
  have hFt : ((.x14 ↦ᵣ (curTop + signExtend12 negOff)) ** (cell ↦ₘ curTop) **
      (flag ↦ₘ f0) : Assertion).pcFree := by pcFree
  have h_t2 := cpsTripleWithin_frameR
    (⌜¬BitVec.ult (curTop + signExtend12 negOff) sp⌝) pcFree_pure
    (cpsTripleWithin_extend_code hsub3
      (cpsTripleWithin_frameR
        ((.x14 ↦ᵣ (curTop + signExtend12 negOff)) ** (cell ↦ₘ curTop) ** (flag ↦ₘ f0))
        hFt h_handler))
  -- `hla2` is already in `stackGuardHalt`'s `hbase + 4 + …` shape (hbase = base+20).
  have h_halt := stackGuardHalt hi2 lo2 (base + 20) flag v5 v6 x1_init f0 hla2
  have hFf : ((.x12 ↦ᵣ sp) ** P' ** (.x10 ↦ᵣ x10_init) **
      (.x14 ↦ᵣ (curTop + signExtend12 negOff)) ** (cell ↦ₘ curTop) : Assertion).pcFree := by
    repeat first
      | apply pcFree_sepConj
      | exact hP'free
      | exact pcFree_regIs
      | exact pcFree_memIs
  have h_f3 := cpsTripleWithin_mono_nSteps hn
    (cpsTripleWithin_frameR
      (⌜BitVec.ult (curTop + signExtend12 negOff) sp⌝) pcFree_pure
      (cpsTripleWithin_extend_code hsub2
        (cpsTripleWithin_frameR
          ((.x12 ↦ᵣ sp) ** P' ** (.x10 ↦ᵣ x10_init) **
            (.x14 ↦ᵣ (curTop + signExtend12 negOff)) ** (cell ↦ₘ curTop))
          hFf h_halt)))
  -- Merge the two paths (both exit at x1_init &&& ~~~1) and align shapes.
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsBranchWithin_merge_same_cr hbr2
      (cpsTripleWithin_weaken (fun _ hp => by xperm_pure hp)
        (fun h hq => by
          obtain ⟨hq', hfact⟩ := (sepConj_pure_right h).mp hq
          rw [if_neg hfact]
          exact hq')
        h_t2)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_pure hp)
        (fun h hq => by
          obtain ⟨hq', hfact⟩ := (sepConj_pure_right h).mp hq
          rw [if_pos hfact]
          xperm_hyp hq')
        h_f3))
-- ============================================================================
-- 4. Concrete instance — guarded ADD (0x01)
-- ============================================================================

/-- Guarded handler-level spec for `h_ADD` (opcode 0x01): the
    stack-underflow guard prologue (word count 2, so `negOff = -64`)
    followed by the verified clean-ret ADD handler of
    `evmAddHandlerSpec`. The post is conditional on the underflow check:
    on underflow the halt flag is set to 7 and the EVM state (operand
    window, `x10`, `x1`, `x12`) is untouched; otherwise the ADD post holds
    and the flag cell is unchanged. -/
theorem evmAddGuardedHandlerSpec (sp base cell flag : Word)
    (hi1 : BitVec 20) (lo1 : BitVec 12) (hi2 : BitVec 20) (lo2 : BitVec 12)
    (hla1 : base + ((hi1.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo1 = cell)
    -- `base + 20 + 4` is the `AUIPC x6` address `base + 24` (offset 24 in the
    -- handler); stated in `+ 20 + 4` form so it feeds `stackGuardHalt`
    -- (`hbase + 4`, `hbase = base + 20`) with no numeral-regroup bridge.
    (hla2 : base + 20 + 4 + ((hi2.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
              + signExtend12 lo2 = flag)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (v7 v6 v5 v11 : Word)
    (x10_init x14_init x1_init curTop f0 : Word) :
    let sum0 := a0 + b0
    let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
    let psum1 := a1 + b1
    let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
    let result1 := psum1 + carry0
    let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
    let carry1 := carry1a ||| carry1b
    let psum2 := a2 + b2
    let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
    let result2 := psum2 + carry1
    let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
    let carry2 := carry2a ||| carry2b
    let psum3 := a3 + b3
    let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
    let result3 := psum3 + carry2
    let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
    let carry3 := carry3a ||| carry3b
    cpsTripleWithin 42 base (x1_init &&& ~~~1)
      (guardedCleanRetHandlerCode base hi1 lo1 hi2 lo2 (-64) EvmAsm.Evm64.evm_add 1)
      ((((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
          ((.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
           (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
           ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) **
           ((sp + 56) ↦ₘ b3))) **
         (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init)) **
        (.x14 ↦ᵣ x14_init) ** (cell ↦ₘ curTop) ** (flag ↦ₘ f0))
      (if BitVec.ult (curTop + signExtend12 (-64 : BitVec 12)) sp then
        -- Underflow: halt flag := 7, handler body skipped; operand window,
        -- x10 (code pointer NOT advanced) and x1 all unchanged.
        (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (7 : Word)) ** (.x6 ↦ᵣ flag) **
          ((.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
           (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
           ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) **
           ((sp + 56) ↦ₘ b3))) **
         (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init)) **
        (.x14 ↦ᵣ (curTop + signExtend12 (-64 : BitVec 12))) ** (cell ↦ₘ curTop) **
        (flag ↦ₘ (7 : Word))
      else
        -- No underflow: the evmAddHandlerSpec post; flag cell unchanged.
        (((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ carry3b) **
          (.x5 ↦ᵣ carry3) ** (.x11 ↦ᵣ carry3a) **
          (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
          ((sp + 32) ↦ₘ sum0) ** ((sp + 40) ↦ₘ result1) ** ((sp + 48) ↦ₘ result2) **
          ((sp + 56) ↦ₘ result3)) **
         (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) **
        (.x14 ↦ᵣ (curTop + signExtend12 (-64 : BitVec 12))) ** (cell ↦ₘ curTop) **
        (flag ↦ₘ f0)) := by
  intro sum0 carry0 psum1 carry1a result1 carry1b carry1 psum2 carry2a result2
    carry2b carry2 psum3 carry3a result3 carry3b carry3
  have h_add := evmAddHandlerSpec sp (base + 40) a0 a1 a2 a3 b0 b1 b2 b3
    v7 v6 v5 v11 x10_init x1_init
  -- Reshape the ADD pre into the template-canonical order (x12/x5/x6 in front).
  have h_add' : cpsTripleWithin 32 (base + 40) (x1_init &&& ~~~1)
      (cleanRetHandlerCode (base + 40) EvmAsm.Evm64.evm_add 1)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
         ((.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
          (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
          ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) **
          ((sp + 56) ↦ₘ b3))) **
        (.x10 ↦ᵣ x10_init) ** (.x1 ↦ᵣ x1_init))
      (((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ carry3b) **
        (.x5 ↦ᵣ carry3) ** (.x11 ↦ᵣ carry3a) **
        (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ sum0) ** ((sp + 40) ↦ₘ result1) ** ((sp + 48) ↦ₘ result2) **
        ((sp + 56) ↦ₘ result3)) **
       (.x10 ↦ᵣ (x10_init + 1)) ** (.x1 ↦ᵣ x1_init)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) h_add
  exact cpsTripleWithin_mono_nSteps (by omega)
    (guardedCleanRetHandlerSpec hi1 lo1 hi2 lo2 (-64) (by omega) (by pcFree)
      (by decide) hla1 hla2 v5 v6 x10_init x1_init x14_init curTop f0 h_add')

-- Axiom audit: `stackGuardBranch`, `stackGuardHalt`,
-- `guardedCleanRetHandlerSpec`, and `evmAddGuardedHandlerSpec` each kernel-
-- depend only on `[propext, Classical.choice, Quot.sound]` (verified by
-- `scripts/port-check.sh` / `scripts/check-axioms.sh`; `#print axioms` omitted
-- here to keep re-elaboration output-free per the zero-warning policy).

end EvmAsm.Codegen.Proofs
