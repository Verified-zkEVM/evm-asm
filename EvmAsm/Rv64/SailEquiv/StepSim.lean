/-
  EvmAsm.Rv64.SailEquiv.StepSim

  Consolidated step-simulation theorem: a single object subsuming the per-instruction
  `*_sail_equiv` lemmas, stated over the hand-written `Instr` AST + `toSailInstr?`
  bridge rather than the individual SAIL `execute_*` entry points.

  ## Scope (tiers)

  The 49 `Instr` constructors that `toSailInstr?` maps (everything except the pseudo
  `MV`/`LI`/`NOP` and the ZisK accelerator call `CSRS`, which map to `none`) split by
  the preconditions their equivalence
  needs — a consequence of `StateRel` tracking only the 32 integer registers and
  memory (NOT the PC or any CSR):

  * **Unconditional (29)** — ALU (`ADD … SLTU`, `LUI`, `ADDIW`, `MUL`), immediate
    (`ADDI … SLTIU`), shift-immediate (`SLLI`/`SRLI`/`SRAI`), and M-extension
    (`MULH … REMU`). These follow from `StateRel` alone. **This file proves these.**
  * **Control-flow (9)** — `AUIPC` (needs PC agreement), the six conditional branches
    and `JAL`/`JALR` (PC/`nextPC`/`misa` agreement + jump-target alignment). Covered
    by the per-instruction lemmas in `BranchProofs`/`ALUProofs` under their explicit
    hypotheses; folding them in needs a strengthened invariant (PC + CSR agreement).
  * **Memory (11)** — `LOAD`/`STORE`. The `MemProofs` lemmas are conditional on an
    `h_exec` hypothesis (the deep bare-mode `vmem_read/write` reduction is deferred).

  See `docs/agents/sail-phase4-bootstrap.md` and the adversarial review for the
  precondition map and the planned strengthened-invariant design for the other tiers.
-/

import EvmAsm.Rv64.SailEquiv.InstrMap
import EvmAsm.Rv64.SailEquiv.ALUProofs
import EvmAsm.Rv64.SailEquiv.ImmProofs
import EvmAsm.Rv64.SailEquiv.ShiftProofs
import EvmAsm.Rv64.SailEquiv.MExtProofs
import EvmAsm.Rv64.Execution

open Out.Functions
open Sail

namespace EvmAsm.Rv64

/-- Instructions whose SAIL-equivalence is unconditional — provable from `StateRel`
    alone (register + memory agreement), with no PC/CSR/alignment side conditions.

    Excludes: the 7 system/pseudo constructors (`ECALL`/`EBREAK`/`FENCE`/`MV`/`LI`/
    `NOP`/`CSRS` — the last is the ZisK accelerator call, outside the SAIL bridge);
    the 11 memory ops (need the bare-mode `vmem` discharge); and the 9
    control-flow ops (`AUIPC`, the conditional branches, `JAL`, `JALR` — need PC/CSR
    agreement and jump-target alignment). -/
def Instr.simulableUncond : Instr → Bool
  | .ECALL | .EBREAK | .FENCE | .MV .. | .LI .. | .NOP | .CSRS .. => false
  | .LD .. | .LW .. | .LWU .. | .LB .. | .LBU .. | .LH .. | .LHU .. => false
  | .SD .. | .SW .. | .SB .. | .SH .. => false
  | .AUIPC .. => false
  | .BEQ .. | .BNE .. | .BLT .. | .BGE .. | .BLTU .. | .BGEU .. => false
  | .JAL .. | .JALR .. => false
  | _ => true

namespace SailEquiv

-- `sim_step`: reduce `execute si` for an unconditional `i` and close via its
-- per-instruction lemma. `simp only [execute]` turns `execute (instruction.FOO …)`
-- into the exact `execute_FOO …` the lemma is stated over (the match is definitional).
set_option hygiene false in
local macro "sim_step" lemma:term : tactic =>
  `(tactic| (simp only [toSailInstr?, Option.some.injEq] at h
             subst h
             simp only [execute]
             apply $lemma <;> first | exact hrel | exact h_nextpc))

-- `no_sim`: discharge an excluded (non-`simulableUncond`) case — `simulableUncond i`
-- reduces to `false`, contradicting `huncond`.
set_option hygiene false in
local macro "no_sim" : tactic =>
  `(tactic| exact absurd huncond (by simp only [Instr.simulableUncond]; decide))

set_option maxHeartbeats 800000 in
/-- **Consolidated step-simulation theorem (unconditional tier).**

    For every `Instr` whose equivalence holds from `StateRel` alone, executing the
    bridged SAIL instruction `si = toSailInstr? i` retires successfully and lands in a
    state related (by `StateRel`) to the toy model's `execInstrBr` result, preserving
    `nextPC` agreement (the per-instruction lemmas thread `nextPC = pc + 4` through, so
    the consolidated form does too). One object subsuming the 29 unconditional
    per-instruction `*_sail_equiv` lemmas. -/
theorem step_execute_sail_sim_uncond
    (sRv : MachineState) (sSail : SailState) (hrel : StateRel sRv sSail)
    (h_nextpc : sSail.regs.get? Register.nextPC = some (sRv.pc + 4))
    (i : Instr) (si : SailInstr)
    (h : toSailInstr? i = some si)
    (huncond : i.simulableUncond = true) :
    ∃ sSail',
      runSail (execute si) sSail = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv i) sSail' ∧
      sSail'.regs.get? Register.nextPC = some (sRv.pc + 4) := by
  cases i with
  | ADD _ _ _    => sim_step add_sail_equiv
  | SUB _ _ _    => sim_step sub_sail_equiv
  | SLL _ _ _    => sim_step sll_sail_equiv
  | SRL _ _ _    => sim_step srl_sail_equiv
  | SRA _ _ _    => sim_step sra_sail_equiv
  | AND _ _ _    => sim_step and_sail_equiv
  | OR _ _ _     => sim_step or_sail_equiv
  | XOR _ _ _    => sim_step xor_sail_equiv
  | SLT _ _ _    => sim_step slt_sail_equiv
  | SLTU _ _ _   => sim_step sltu_sail_equiv
  | ADDI _ _ _   => sim_step addi_sail_equiv
  | ANDI _ _ _   => sim_step andi_sail_equiv
  | ORI _ _ _    => sim_step ori_sail_equiv
  | XORI _ _ _   => sim_step xori_sail_equiv
  | SLTI _ _ _   => sim_step slti_sail_equiv
  | SLTIU _ _ _  => sim_step sltiu_sail_equiv
  | SLLI _ _ _   => sim_step slli_sail_equiv
  | SRLI _ _ _   => sim_step srli_sail_equiv
  | SRAI _ _ _   => sim_step srai_sail_equiv
  | LUI _ _      => sim_step lui_sail_equiv
  | AUIPC _ _    => no_sim
  | LD _ _ _     => no_sim
  | SD _ _ _     => no_sim
  | LW _ _ _     => no_sim
  | LWU _ _ _    => no_sim
  | SW _ _ _     => no_sim
  | LB _ _ _     => no_sim
  | LH _ _ _     => no_sim
  | LBU _ _ _    => no_sim
  | LHU _ _ _    => no_sim
  | SB _ _ _     => no_sim
  | SH _ _ _     => no_sim
  | BEQ _ _ _    => no_sim
  | BNE _ _ _    => no_sim
  | BLT _ _ _    => no_sim
  | BGE _ _ _    => no_sim
  | BLTU _ _ _   => no_sim
  | BGEU _ _ _   => no_sim
  | JAL _ _      => no_sim
  | JALR _ _ _   => no_sim
  | MV _ _       => no_sim
  | LI _ _       => no_sim
  | NOP          => no_sim
  | CSRS _ _     => no_sim
  | ADDIW _ _ _  => sim_step addiw_sail_equiv
  | ECALL        => no_sim
  | FENCE        => no_sim
  | EBREAK       => no_sim
  | MUL _ _ _    => sim_step mul_sail_equiv
  | MULH _ _ _   => sim_step mulh_sail_equiv
  | MULHSU _ _ _ => sim_step mulhsu_sail_equiv
  | MULHU _ _ _  => sim_step mulhu_sail_equiv
  | DIV _ _ _    => sim_step div_sail_equiv
  | DIVU _ _ _   => sim_step divu_sail_equiv
  | REM _ _ _    => sim_step rem_sail_equiv
  | REMU _ _ _   => sim_step remu_sail_equiv

end SailEquiv
end EvmAsm.Rv64
