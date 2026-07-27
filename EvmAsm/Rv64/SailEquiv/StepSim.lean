/-
  EvmAsm.Rv64.SailEquiv.StepSim

  Consolidated step-simulation theorem: a single object subsuming the per-instruction
  `*_sail_equiv` lemmas, stated over the hand-written `Instr` AST + `toSailInstr?`
  bridge rather than the individual SAIL `execute_*` entry points.

  ## Scope (tiers)

  The 49 `Instr` constructors that `toSailInstr?` maps (everything except the pseudo
  `MV`/`LI`/`NOP` and the ZisK accelerator call `CSRS`, which map to `none`) split by
  the preconditions their equivalence needs:

  * **Unconditional (29)** — ALU (`ADD … SLTU`, `LUI`, `ADDIW`, `MUL`), immediate
    (`ADDI … SLTIU`), shift-immediate (`SLLI`/`SRLI`/`SRAI`), and M-extension
    (`MULH … REMU`). These follow from `StateRel` alone;
    `step_execute_sail_sim_uncond` covers exactly this tier.
  * **Control-flow (9)** — `AUIPC`, the six conditional branches, `JAL`, `JALR`.
    Need PC/`nextPC`/`misa` agreement and jump-target alignment (per-instruction
    lemmas in `BranchProofs`/`ALUProofs`).
  * **Memory (11)** — `LOAD`/`STORE`. Need `BareModeInv` plus access-local
    PMA/MMIO/alignment facts — and, for loads only, byte-presence witnesses
    (per-instruction capstones in `VmemReduction.lean` / `VmemReductionLoads.lean` /
    `VmemReductionStores.lean`).

  The full theorem `step_execute_sail_sim` (bottom of this file) already folds
  **all 49** in: the strengthened invariant exists — it is `StateRelPC`
  (registers + memory + committed PC) — and the per-instruction facts are
  packaged as `instrSideCond`. What remains is discharging its hypotheses from
  a run-level invariant rather than per access/step: the load byte-presence
  witnesses (#10529) and the fetch-side `nextPC = pc + 4` default (#10530).

  See `docs/agents/sail-phase4-bootstrap.md` for the precondition map.
-/

import EvmAsm.Rv64.SailEquiv.InstrMap
import EvmAsm.Rv64.SailEquiv.ALUProofs
import EvmAsm.Rv64.SailEquiv.BranchProofs
import EvmAsm.Rv64.SailEquiv.ImmProofs
import EvmAsm.Rv64.SailEquiv.ShiftProofs
import EvmAsm.Rv64.SailEquiv.MExtProofs
import EvmAsm.Rv64.SailEquiv.VmemReductionLoads
import EvmAsm.Rv64.SailEquiv.VmemReductionStores
import EvmAsm.Rv64.Execution

open Out.Functions
open Sail

namespace EvmAsm.Rv64

/-- Instructions whose SAIL-equivalence is unconditional — provable from `StateRel`
    alone (register + memory agreement), with no PC/CSR/alignment side conditions.

    Excludes: the 7 system/pseudo constructors (`ECALL`/`EBREAK`/`FENCE`/`MV`/`LI`/
    `NOP`/`CSRS` — the last is the ZisK accelerator call, outside the SAIL bridge);
    the 11 memory ops (unconditional, but under `BareModeInv` + per-access facts);
    and the 9 control-flow ops (`AUIPC`, the conditional branches, `JAL`, `JALR` —
    need PC/CSR agreement and jump-target alignment). -/
def Instr.simulableUncond : Instr → Bool
  | .ECALL | .EBREAK | .FENCE | .MV .. | .LI .. | .NOP | .CSRS .. => false
  | .LD .. | .LW .. | .LWU .. | .LB .. | .LBU .. | .LH .. | .LHU .. => false
  | .SD .. | .SW .. | .SB .. | .SH .. => false
  | .AUIPC .. => false
  | .BEQ .. | .BNE .. | .BLT .. | .BGE .. | .BLTU .. | .BGEU .. => false
  | .JAL .. | .JALR .. => false
  | _ => true

/-- Instructions covered by the full `execute` simulation theorem below.

    This includes the register-only tier, AUIPC/branches/jumps, and all memory
    loads/stores. It excludes pseudo/unmapped constructors and the system
    instructions whose Sail behavior intentionally diverges from the toy model. -/
def Instr.simulable : Instr → Bool
  | .ECALL | .EBREAK | .FENCE | .MV .. | .LI .. | .NOP | .CSRS .. => false
  | _ => true

namespace SailEquiv

/-- Per-instruction side conditions for the full `execute` simulation theorem.

    Register-only instructions need no extra facts. Control-flow instructions need
    the PC/CSR/alignment facts already exposed by their per-instruction lemmas.
    Memory instructions need the bare-mode platform bundle plus the access-local
    PMA/MMIO/alignment facts, and loads additionally need byte-presence witnesses. -/
def instrSideCond (i : Instr) (sRv : MachineState) (sSail : SailState) : Prop :=
  match i with
  | .AUIPC .. => True
  | .BEQ _ _ offset | .BNE _ _ offset | .BLT _ _ offset | .BGE _ _ offset
  | .BLTU _ _ offset | .BGEU _ _ offset =>
      (∃ v, sSail.regs.get? Register.misa = some v) ∧
      (sRv.pc + signExtend13 offset) &&& 3 = 0
  | .JAL _ offset =>
      (∃ v, sSail.regs.get? Register.misa = some v) ∧
      (sRv.pc + signExtend21 offset) &&& 3 = 0
  | .JALR _ rs1 offset =>
      (∃ s_mid, update_elp_state (regToRegidx rs1) sSail = .ok () s_mid ∧
        StateRel sRv s_mid ∧
        s_mid.regs.get? Register.PC = some sRv.pc ∧
        s_mid.regs.get? Register.nextPC = some (sRv.pc + 4) ∧
        (∃ v, s_mid.regs.get? Register.misa = some v)) ∧
      ((sRv.getReg rs1 + signExtend12 offset) &&& ~~~1#64) &&& 3 = 0
  | .LD _ rs1 offset =>
      ∃ (bm : BareModeInv sSail) (region : PMA_Region)
        (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8),
        is_aligned_vaddr (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset)) 8 = true ∧
        matching_pma_region bm.regions
          (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8 = some region ∧
        region.attributes.readable = true ∧
        is_aligned_paddr (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8 = true ∧
        (within_clint (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8) sSail
          = .ok false sSail ∧
        (within_sig (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8) sSail
          = .ok false sSail ∧
        (within_htif_readable (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8) sSail
          = .ok false sSail ∧
        sSail.mem.get? (sRv.getReg rs1 + signExtend12 offset).toNat = some b0 ∧
        sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+1) = some b1 ∧
        sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+2) = some b2 ∧
        sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+3) = some b3 ∧
        sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+4) = some b4 ∧
        sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+5) = some b5 ∧
        sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+6) = some b6 ∧
        sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+7) = some b7
  | .LW _ rs1 offset | .LWU _ rs1 offset =>
      ∃ (bm : BareModeInv sSail) (region : PMA_Region) (b0 b1 b2 b3 : BitVec 8),
        is_aligned_vaddr (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset)) 4 = true ∧
        matching_pma_region bm.regions
          (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4 = some region ∧
        region.attributes.readable = true ∧
        is_aligned_paddr (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4 = true ∧
        (within_clint (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4) sSail
          = .ok false sSail ∧
        (within_sig (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4) sSail
          = .ok false sSail ∧
        (within_htif_readable (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4) sSail
          = .ok false sSail ∧
        sSail.mem.get? (sRv.getReg rs1 + signExtend12 offset).toNat = some b0 ∧
        sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+1) = some b1 ∧
        sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+2) = some b2 ∧
        sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+3) = some b3
  | .LH _ rs1 offset | .LHU _ rs1 offset =>
      ∃ (bm : BareModeInv sSail) (region : PMA_Region) (b0 b1 : BitVec 8),
        is_aligned_vaddr (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset)) 2 = true ∧
        matching_pma_region bm.regions
          (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2 = some region ∧
        region.attributes.readable = true ∧
        is_aligned_paddr (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2 = true ∧
        (within_clint (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2) sSail
          = .ok false sSail ∧
        (within_sig (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2) sSail
          = .ok false sSail ∧
        (within_htif_readable (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2) sSail
          = .ok false sSail ∧
        sSail.mem.get? (sRv.getReg rs1 + signExtend12 offset).toNat = some b0 ∧
        sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+1) = some b1
  | .LB _ rs1 offset | .LBU _ rs1 offset =>
      ∃ (bm : BareModeInv sSail) (region : PMA_Region) (b0 : BitVec 8),
        is_aligned_vaddr (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset)) 1 = true ∧
        matching_pma_region bm.regions
          (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1 = some region ∧
        region.attributes.readable = true ∧
        is_aligned_paddr (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1 = true ∧
        (within_clint (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1) sSail
          = .ok false sSail ∧
        (within_sig (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1) sSail
          = .ok false sSail ∧
        (within_htif_readable (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1) sSail
          = .ok false sSail ∧
        sSail.mem.get? (sRv.getReg rs1 + signExtend12 offset).toNat = some b0
  | .SD rs1 _ offset =>
      ∃ (bm : BareModeInv sSail) (region : PMA_Region),
        is_aligned_vaddr (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset)) 8 = true ∧
        matching_pma_region bm.regions
          (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8 = some region ∧
        region.attributes.writable = true ∧
        is_aligned_paddr (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8 = true ∧
        (within_clint (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8) sSail
          = .ok false sSail ∧
        (within_sig (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8) sSail
          = .ok false sSail ∧
        (within_htif_writable (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8) sSail
          = .ok false sSail
  | .SW rs1 _ offset =>
      ∃ (bm : BareModeInv sSail) (region : PMA_Region),
        is_aligned_vaddr (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset)) 4 = true ∧
        matching_pma_region bm.regions
          (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4 = some region ∧
        region.attributes.writable = true ∧
        is_aligned_paddr (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4 = true ∧
        (within_clint (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4) sSail
          = .ok false sSail ∧
        (within_sig (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4) sSail
          = .ok false sSail ∧
        (within_htif_writable (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4) sSail
          = .ok false sSail
  | .SH rs1 _ offset =>
      ∃ (bm : BareModeInv sSail) (region : PMA_Region),
        is_aligned_vaddr (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset)) 2 = true ∧
        matching_pma_region bm.regions
          (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2 = some region ∧
        region.attributes.writable = true ∧
        is_aligned_paddr (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2 = true ∧
        (within_clint (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2) sSail
          = .ok false sSail ∧
        (within_sig (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2) sSail
          = .ok false sSail ∧
        (within_htif_writable (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2) sSail
          = .ok false sSail
  | .SB rs1 _ offset =>
      ∃ (bm : BareModeInv sSail) (region : PMA_Region),
        is_aligned_vaddr (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset)) 1 = true ∧
        matching_pma_region bm.regions
          (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1 = some region ∧
        region.attributes.writable = true ∧
        is_aligned_paddr (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1 = true ∧
        (within_clint (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1) sSail
          = .ok false sSail ∧
        (within_sig (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1) sSail
          = .ok false sSail ∧
        (within_htif_writable (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1) sSail
          = .ok false sSail
  | _ => True

-- `sim_step`: reduce `execute si` for an unconditional `i` and close via its
-- per-instruction lemma. `simp only [execute]` turns `execute (instruction.FOO …)`
-- into the exact `execute_FOO …` the lemma is stated over (the match is definitional).
set_option hygiene false in
local macro "sim_step" lem:term : tactic =>
  `(tactic| (simp only [toSailInstr?, Option.some.injEq] at h
             subst h
             simp only [execute]
             apply $lem <;> first | exact hrel | exact h_nextpc))

-- `no_sim`: discharge an excluded (non-`simulableUncond`) case — `simulableUncond i`
-- reduces to `false`, contradicting `huncond`.
set_option hygiene false in
local macro "no_sim" : tactic =>
  `(tactic| exact absurd huncond (by simp [Instr.simulableUncond]))

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

theorem step_execute_sail_sim_of_uncond
    (sRv : MachineState) (sSail : SailState) (hrel : StateRel sRv sSail)
    (h_nextpc : sSail.regs.get? Register.nextPC = some (sRv.pc + 4))
    (i : Instr) (si : SailInstr)
    (h : toSailInstr? i = some si)
    (huncond : i.simulableUncond = true) :
    ∃ sSail',
      runSail (execute si) sSail = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv i) sSail' ∧
      sSail'.regs.get? Register.nextPC = some (execInstrBr sRv i).pc := by
  exact Exists.elim (step_execute_sail_sim_uncond sRv sSail hrel h_nextpc i si h huncond) (by
    intro sSail' hpair
    have h_pc : (execInstrBr sRv i).pc = sRv.pc + 4 := by
      cases i <;> simp [Instr.simulableUncond, execInstrBr, MachineState.setPC] at huncond ⊢
    exact ⟨sSail', hpair.left, hpair.right.left, by simpa [h_pc] using hpair.right.right⟩)

/-- **Consolidated `execute` simulation theorem.**

    Covers every non-system instruction mapped by `toSailInstr?`: the unconditional
    register-only tier, AUIPC/branches/jumps, and all loads/stores. The postcondition
    keeps the relation at the `execute_*` boundary: registers/memory agree via
    `StateRel`, and Sail `nextPC` equals the toy post-state PC. A caller that wants a
    committed-PC `StateRelPC` state can compose this with `tick_pc` via
    `StepProofs.step_of_execute`. -/
theorem step_execute_sail_sim
    (sRv : MachineState) (sSail : SailState) (hrelpc : StateRelPC sRv sSail)
    (h_nextpc : sSail.regs.get? Register.nextPC = some (sRv.pc + 4))
    (i : Instr) (si : SailInstr)
    (h : toSailInstr? i = some si)
    (hsim : i.simulable = true)
    (hside : instrSideCond i sRv sSail) :
    ∃ sSail',
      runSail (execute si) sSail = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv i) sSail' ∧
      sSail'.regs.get? Register.nextPC = some (execInstrBr sRv i).pc := by
  cases i with
  | ADD _ _ _    => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | SUB _ _ _    => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | SLL _ _ _    => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | SRL _ _ _    => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | SRA _ _ _    => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | AND _ _ _    => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | OR _ _ _     => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | XOR _ _ _    => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | SLT _ _ _    => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | SLTU _ _ _   => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | ADDI _ _ _   => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | ANDI _ _ _   => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | ORI _ _ _    => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | XORI _ _ _   => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | SLTI _ _ _   => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | SLTIU _ _ _  => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | SLLI _ _ _   => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | SRLI _ _ _   => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | SRAI _ _ _   => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | LUI _ _      => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | ADDIW _ _ _  => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | MUL _ _ _    => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | MULH _ _ _   => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | MULHSU _ _ _ => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | MULHU _ _ _  => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | DIV _ _ _    => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | DIVU _ _ _   => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | REM _ _ _    => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | REMU _ _ _   => exact step_execute_sail_sim_of_uncond sRv sSail hrelpc.toStateRel h_nextpc _ _ h (by simp [Instr.simulableUncond])
  | AUIPC rd imm =>
      simp only [toSailInstr?, Option.some.injEq] at h
      subst h
      simp only [execute]
      exact Exists.elim
        (auipc_sail_equiv sRv sSail hrelpc.toStateRel h_nextpc hrelpc.pc_agree rd imm) (by
        intro sSail' hpair
        refine ⟨sSail', hpair.left, hpair.right.left, ?_⟩
        simpa [execInstrBr, MachineState.setPC] using hpair.right.right)
  | BEQ rs1 rs2 offset =>
      simp only [toSailInstr?, Option.some.injEq] at h
      subst h
      simp only [execute]
      rcases hside with ⟨h_misa, h_align⟩
      exact beq_sail_equiv sRv sSail hrelpc.toStateRel hrelpc.pc_agree h_nextpc
        h_misa rs1 rs2 offset h_align
  | BNE rs1 rs2 offset =>
      simp only [toSailInstr?, Option.some.injEq] at h
      subst h
      simp only [execute]
      rcases hside with ⟨h_misa, h_align⟩
      exact bne_sail_equiv sRv sSail hrelpc.toStateRel hrelpc.pc_agree h_nextpc
        h_misa rs1 rs2 offset h_align
  | BLT rs1 rs2 offset =>
      simp only [toSailInstr?, Option.some.injEq] at h
      subst h
      simp only [execute]
      rcases hside with ⟨h_misa, h_align⟩
      exact blt_sail_equiv sRv sSail hrelpc.toStateRel hrelpc.pc_agree h_nextpc
        h_misa rs1 rs2 offset h_align
  | BGE rs1 rs2 offset =>
      simp only [toSailInstr?, Option.some.injEq] at h
      subst h
      simp only [execute]
      rcases hside with ⟨h_misa, h_align⟩
      exact bge_sail_equiv sRv sSail hrelpc.toStateRel hrelpc.pc_agree h_nextpc
        h_misa rs1 rs2 offset h_align
  | BLTU rs1 rs2 offset =>
      simp only [toSailInstr?, Option.some.injEq] at h
      subst h
      simp only [execute]
      rcases hside with ⟨h_misa, h_align⟩
      exact bltu_sail_equiv sRv sSail hrelpc.toStateRel hrelpc.pc_agree h_nextpc
        h_misa rs1 rs2 offset h_align
  | BGEU rs1 rs2 offset =>
      simp only [toSailInstr?, Option.some.injEq] at h
      subst h
      simp only [execute]
      rcases hside with ⟨h_misa, h_align⟩
      exact bgeu_sail_equiv sRv sSail hrelpc.toStateRel hrelpc.pc_agree h_nextpc
        h_misa rs1 rs2 offset h_align
  | JAL rd offset =>
      simp only [toSailInstr?, Option.some.injEq] at h
      subst h
      simp only [execute]
      rcases hside with ⟨h_misa, h_align⟩
      exact jal_sail_equiv sRv sSail hrelpc.toStateRel hrelpc.pc_agree h_nextpc
        h_misa rd offset h_align
  | JALR rd rs1 offset =>
      simp only [toSailInstr?, Option.some.injEq] at h
      subst h
      simp only [execute]
      rcases hside with ⟨h_elp, h_align⟩
      exact jalr_sail_equiv sRv sSail rd rs1 offset h_elp h_align
  | LD rd rs1 offset =>
      simp only [toSailInstr?, Option.some.injEq] at h
      subst h
      simp only [execute]
      rcases hside with
        ⟨bm, region, b0, b1, b2, b3, b4, b5, b6, b7, h_valign, h_match, h_read,
          h_palign, hclint, hsig, hhtif, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7⟩
      exact Exists.elim (ld_sail_equiv sRv sSail rd rs1 offset hrelpc.toStateRel bm region
          b0 b1 b2 b3 b4 b5 b6 b7 h_valign h_match h_read h_palign hclint hsig hhtif
          hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7) (fun sSail' hpair => by
          refine ⟨sSail', hpair.left, hpair.right.left, ?_⟩
          rw [hpair.right.right, h_nextpc]
          simp [execInstrBr, MachineState.setPC])
  | LW rd rs1 offset =>
      simp only [toSailInstr?, Option.some.injEq] at h
      subst h
      simp only [execute]
      rcases hside with
        ⟨bm, region, b0, b1, b2, b3, h_valign, h_match, h_read, h_palign, hclint,
          hsig, hhtif, hm0, hm1, hm2, hm3⟩
      cases lw_sail_equiv sRv sSail rd rs1 offset hrelpc.toStateRel bm region
          b0 b1 b2 b3 h_valign h_match h_read h_palign hclint hsig hhtif
          hm0 hm1 hm2 hm3 with
      | intro sSail' hpair =>
          refine ⟨sSail', hpair.left, hpair.right.left, ?_⟩
          rw [hpair.right.right, h_nextpc]
          simp [execInstrBr, MachineState.setPC]
  | LWU rd rs1 offset =>
      simp only [toSailInstr?, Option.some.injEq] at h
      subst h
      simp only [execute]
      rcases hside with
        ⟨bm, region, b0, b1, b2, b3, h_valign, h_match, h_read, h_palign, hclint,
          hsig, hhtif, hm0, hm1, hm2, hm3⟩
      cases lwu_sail_equiv sRv sSail rd rs1 offset hrelpc.toStateRel bm region
          b0 b1 b2 b3 h_valign h_match h_read h_palign hclint hsig hhtif
          hm0 hm1 hm2 hm3 with
      | intro sSail' hpair =>
          refine ⟨sSail', hpair.left, hpair.right.left, ?_⟩
          rw [hpair.right.right, h_nextpc]
          simp [execInstrBr, MachineState.setPC]
  | LH rd rs1 offset =>
      simp only [toSailInstr?, Option.some.injEq] at h
      subst h
      simp only [execute]
      rcases hside with
        ⟨bm, region, b0, b1, h_valign, h_match, h_read, h_palign, hclint, hsig,
          hhtif, hm0, hm1⟩
      cases lh_sail_equiv sRv sSail rd rs1 offset hrelpc.toStateRel bm region
          b0 b1 h_valign h_match h_read h_palign hclint hsig hhtif hm0 hm1 with
      | intro sSail' hpair =>
          refine ⟨sSail', hpair.left, hpair.right.left, ?_⟩
          rw [hpair.right.right, h_nextpc]
          simp [execInstrBr, MachineState.setPC]
  | LHU rd rs1 offset =>
      simp only [toSailInstr?, Option.some.injEq] at h
      subst h
      simp only [execute]
      rcases hside with
        ⟨bm, region, b0, b1, h_valign, h_match, h_read, h_palign, hclint, hsig,
          hhtif, hm0, hm1⟩
      cases lhu_sail_equiv sRv sSail rd rs1 offset hrelpc.toStateRel bm region
          b0 b1 h_valign h_match h_read h_palign hclint hsig hhtif hm0 hm1 with
      | intro sSail' hpair =>
          refine ⟨sSail', hpair.left, hpair.right.left, ?_⟩
          rw [hpair.right.right, h_nextpc]
          simp [execInstrBr, MachineState.setPC]
  | LB rd rs1 offset =>
      simp only [toSailInstr?, Option.some.injEq] at h
      subst h
      simp only [execute]
      rcases hside with
        ⟨bm, region, b0, h_valign, h_match, h_read, h_palign, hclint, hsig, hhtif, hm0⟩
      cases lb_sail_equiv sRv sSail rd rs1 offset hrelpc.toStateRel bm region
          b0 h_valign h_match h_read h_palign hclint hsig hhtif hm0 with
      | intro sSail' hpair =>
          refine ⟨sSail', hpair.left, hpair.right.left, ?_⟩
          rw [hpair.right.right, h_nextpc]
          simp [execInstrBr, MachineState.setPC]
  | LBU rd rs1 offset =>
      simp only [toSailInstr?, Option.some.injEq] at h
      subst h
      simp only [execute]
      rcases hside with
        ⟨bm, region, b0, h_valign, h_match, h_read, h_palign, hclint, hsig, hhtif, hm0⟩
      cases lbu_sail_equiv sRv sSail rd rs1 offset hrelpc.toStateRel bm region
          b0 h_valign h_match h_read h_palign hclint hsig hhtif hm0 with
      | intro sSail' hpair =>
          refine ⟨sSail', hpair.left, hpair.right.left, ?_⟩
          rw [hpair.right.right, h_nextpc]
          simp [execInstrBr, MachineState.setPC]
  | SD rs1 rs2 offset =>
      simp only [toSailInstr?, Option.some.injEq] at h
      subst h
      simp only [execute]
      rcases hside with ⟨bm, region, h_valign, h_match, h_write, h_palign, hclint, hsig, hhtif⟩
      cases sd_sail_equiv sRv sSail rs1 rs2 offset hrelpc.toStateRel bm region
          h_valign h_match h_write h_palign hclint hsig hhtif with
      | intro sSail' hpair =>
          refine ⟨sSail', hpair.left, hpair.right.left, ?_⟩
          rw [hpair.right.right, h_nextpc]
          simp [execInstrBr, MachineState.setPC]
  | SW rs1 rs2 offset =>
      simp only [toSailInstr?, Option.some.injEq] at h
      subst h
      simp only [execute]
      rcases hside with ⟨bm, region, h_valign, h_match, h_write, h_palign, hclint, hsig, hhtif⟩
      cases sw_sail_equiv sRv sSail rs1 rs2 offset hrelpc.toStateRel bm region
          h_valign h_match h_write h_palign hclint hsig hhtif with
      | intro sSail' hpair =>
          refine ⟨sSail', hpair.left, hpair.right.left, ?_⟩
          rw [hpair.right.right, h_nextpc]
          simp [execInstrBr, MachineState.setPC]
  | SH rs1 rs2 offset =>
      simp only [toSailInstr?, Option.some.injEq] at h
      subst h
      simp only [execute]
      rcases hside with ⟨bm, region, h_valign, h_match, h_write, h_palign, hclint, hsig, hhtif⟩
      cases sh_sail_equiv sRv sSail rs1 rs2 offset hrelpc.toStateRel bm region
          h_valign h_match h_write h_palign hclint hsig hhtif with
      | intro sSail' hpair =>
          refine ⟨sSail', hpair.left, hpair.right.left, ?_⟩
          rw [hpair.right.right, h_nextpc]
          simp [execInstrBr, MachineState.setPC]
  | SB rs1 rs2 offset =>
      simp only [toSailInstr?, Option.some.injEq] at h
      subst h
      simp only [execute]
      rcases hside with ⟨bm, region, h_valign, h_match, h_write, h_palign, hclint, hsig, hhtif⟩
      cases sb_sail_equiv sRv sSail rs1 rs2 offset hrelpc.toStateRel bm region
          h_valign h_match h_write h_palign hclint hsig hhtif with
      | intro sSail' hpair =>
          refine ⟨sSail', hpair.left, hpair.right.left, ?_⟩
          rw [hpair.right.right, h_nextpc]
          simp [execInstrBr, MachineState.setPC]
  | MV _ _ =>
      exact absurd hsim (by simp only [Instr.simulable]; decide)
  | LI _ _ =>
      exact absurd hsim (by simp only [Instr.simulable]; decide)
  | NOP =>
      exact absurd hsim (by simp only [Instr.simulable]; decide)
  | ECALL =>
      exact absurd hsim (by simp only [Instr.simulable]; decide)
  | FENCE =>
      exact absurd hsim (by simp only [Instr.simulable]; decide)
  | EBREAK =>
      exact absurd hsim (by simp only [Instr.simulable]; decide)
  | CSRS _ _ =>
      exact absurd hsim (by simp only [Instr.simulable]; decide)

end SailEquiv
end EvmAsm.Rv64
