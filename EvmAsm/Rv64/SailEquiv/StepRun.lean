/-
  EvmAsm.Rv64.SailEquiv.StepRun

  Run-level Rv64 ↔ Sail simulation: lifts the one-instruction capstones to an
  arbitrary number of steps.

  The missing piece was the **fetch-side `nextPC := PC + 4` default**.  Every
  step-level theorem consumes `nextPC = pc + 4` and produces a state whose
  `nextPC` is the branch *target*, so `StateRelPC` cannot be iterated.  In real
  Sail the default is re-installed during fetch; `sailStep` below models exactly
  that (and only that) part of the vendored fetch, so the invariant `RunInv`
  — which carries no `nextPC` fact at all — is genuinely step-stable.
-/

import EvmAsm.Rv64.SailEquiv.RunInv
import EvmAsm.Rv64.SailEquiv.StepSim
import EvmAsm.Rv64.SailEquiv.StepProofs

open Out.Functions
open Sail

namespace EvmAsm.Rv64

/-- Instructions covered by the **run-level** simulation theorem.

    This is `Instr.simulable` minus `JALR`.  `JALR` drops out for a reason that
    is not ours to fix: the vendored `execute_JALR` begins with
    `update_elp_state`, whose `currentlyEnabled Ext_Zicfilp` query cascades into
    `currentlyEnabled Ext_Zicsr`, for which the extracted `currentlyEnabled` has
    **no arm** — it falls through to the generated `assert false; throw` catch-all.
    See `SailEquiv.update_elp_state_error`: the Sail side faults in every state,
    so the `h_elp` premise of `jalr_sail_equiv` (and hence
    `instrSideCond (.JALR ..)`) is unsatisfiable. -/
def Instr.runSimulable : Instr → Bool
  | .JALR .. => false
  | i => i.simulable

/-- Run-simulable instructions are simulable. -/
theorem Instr.simulable_of_runSimulable {i : Instr} (h : i.runSimulable = true) :
    i.simulable = true := by
  cases i <;> simp_all [Instr.runSimulable, Instr.simulable]

namespace SailEquiv

/-- Every simulable instruction is mapped by `toSailInstr?`. -/
theorem toSailInstr?_isSome_of_simulable {i : Instr} (h : i.simulable = true) :
    ∃ si, toSailInstr? i = some si := by
  cases i <;> simp_all [Instr.simulable, toSailInstr?]

/-- A run-simulable instruction's `step` is exactly `execInstrBr`: the only
    `step` guards on this tier are the memory-access checks, and they can only
    turn success into `none`. -/
theorem step_eq_execInstrBr {s s' : MachineState} {i : Instr}
    (hfetch : s.code s.pc = some i) (hsim : i.runSimulable = true)
    (hstep : step s = some s') : s' = execInstrBr s i := by
  cases i
  case JALR _ _ _ => exact absurd hsim (by simp [Instr.runSimulable])
  case ECALL => exact absurd hsim (by simp [Instr.runSimulable, Instr.simulable])
  case EBREAK => exact absurd hsim (by simp [Instr.runSimulable, Instr.simulable])
  case FENCE => exact absurd hsim (by simp [Instr.runSimulable, Instr.simulable])
  case CSRS _ _ => exact absurd hsim (by simp [Instr.runSimulable, Instr.simulable])
  case MV _ _ => exact absurd hsim (by simp [Instr.runSimulable, Instr.simulable])
  case LI _ _ => exact absurd hsim (by simp [Instr.runSimulable, Instr.simulable])
  case NOP => exact absurd hsim (by simp [Instr.runSimulable, Instr.simulable])
  all_goals (
    simp only [step, hfetch] at hstep
    first
      | (simp only [Option.some.injEq] at hstep; exact hstep.symm)
      | (split at hstep
         · simp only [Option.some.injEq] at hstep; exact hstep.symm
         · exact absurd hstep (by simp)))

-- ============================================================================
-- The modelled Sail step
-- ============================================================================

/-- **One modelled Sail step.**

    The fetch-side `nextPC := PC + 4` default (the `F_Base` arm of the vendored
    fetch, which we do not otherwise model — the instruction-*decode* tie
    between the toy `MachineState.code` and Sail's byte memory is roadmap item
    P7 and explicitly out of scope for #10530), then the instruction body, then
    the `tick_pc` `PC := nextPC` commit. -/
noncomputable def sailStep (si : SailInstr) : SailM Unit := do
  let pc ← readReg Register.PC
  set_next_pc (pc + 4)
  let _ ← execute si
  tick_pc ()

/-- `sailStep` reduces to "install the `pc + 4` default, then run
    `execute ; tick_pc`". -/
theorem runSail_sailStep_eq {si : SailInstr} {sSail : SailState} {pc : BitVec 64}
    (h_pc : sSail.regs.get? Register.PC = some pc) :
    runSail (sailStep si) sSail
      = runSail (execute si >>= fun _ => tick_pc ())
          { sSail with regs := sSail.regs.insert Register.nextPC (pc + 4) } := by
  simp only [sailStep, runSail_bind, runSail_readReg_PC h_pc, runSail_set_next_pc]

-- ============================================================================
-- Discharging the per-instruction side conditions from the run invariant
-- ============================================================================

/-- **The run-level invariant discharges every per-instruction Sail side
    condition.** Alignment comes from the toy `isValid*Access` guard (which
    `hguard` witnesses), window membership from `stepSideCond`, and everything
    else from `RunInv` itself. -/
theorem instrSideCond_of_runInv {lo hi : Nat} {sRv : MachineState} {sSail : SailState}
    {i : Instr} (hinv : RunInv lo hi sRv sSail)
    (hlo : RAM_MEM_START ≤ lo) (hhi : hi ≤ RAM_MEM_END)
    (hfetch : sRv.code sRv.pc = some i) (hsim : i.runSimulable = true)
    (hside : stepSideCond lo hi sRv)
    (hguard : step sRv ≠ none) : instrSideCond i sRv sSail := by
  cases i
  case BEQ rs1 rs2 offset =>
    simp only [stepSideCond, hfetch] at hside
    exact ⟨hinv.misa_present, hside⟩
  case BNE rs1 rs2 offset =>
    simp only [stepSideCond, hfetch] at hside
    exact ⟨hinv.misa_present, hside⟩
  case BLT rs1 rs2 offset =>
    simp only [stepSideCond, hfetch] at hside
    exact ⟨hinv.misa_present, hside⟩
  case BGE rs1 rs2 offset =>
    simp only [stepSideCond, hfetch] at hside
    exact ⟨hinv.misa_present, hside⟩
  case BLTU rs1 rs2 offset =>
    simp only [stepSideCond, hfetch] at hside
    exact ⟨hinv.misa_present, hside⟩
  case BGEU rs1 rs2 offset =>
    simp only [stepSideCond, hfetch] at hside
    exact ⟨hinv.misa_present, hside⟩
  case JAL rd offset =>
    simp only [stepSideCond, hfetch] at hside
    exact ⟨hinv.misa_present, hside⟩
  case JALR rd rs1 offset =>
    exact absurd hsim (by simp [Instr.runSimulable])
  case LD rd rs1 offset =>
    simp only [stepSideCond, hfetch] at hside
    obtain ⟨ha1, ha2⟩ := hside
    have hv : isValidDwordAccess (sRv.getReg rs1 + signExtend12 offset) = true := by
      by_contra hc
      exact hguard (step_ld_trap hfetch (by simpa using hc))
    have halign : (sRv.getReg rs1 + signExtend12 offset).toNat % 8 = 0 := by
      simp only [isValidDwordAccess, Bool.and_eq_true, isAligned8, beq_iff_eq] at hv
      exact hv.2
    obtain ⟨bm, hreg, -⟩ := hinv.bare
    obtain ⟨hva, hm, hpa, hcl, hsg, -, hht⟩ := hinv.access_ok hlo hhi ha1 ha2 halign bm hreg
    obtain ⟨b0, hb0⟩ := hinv.byte_present (a := (sRv.getReg rs1 + signExtend12 offset).toNat)
      (by omega) (by omega)
    obtain ⟨b1, hb1⟩ := hinv.byte_present (a := (sRv.getReg rs1 + signExtend12 offset).toNat + 1)
      (by omega) (by omega)
    obtain ⟨b2, hb2⟩ := hinv.byte_present (a := (sRv.getReg rs1 + signExtend12 offset).toNat + 2)
      (by omega) (by omega)
    obtain ⟨b3, hb3⟩ := hinv.byte_present (a := (sRv.getReg rs1 + signExtend12 offset).toNat + 3)
      (by omega) (by omega)
    obtain ⟨b4, hb4⟩ := hinv.byte_present (a := (sRv.getReg rs1 + signExtend12 offset).toNat + 4)
      (by omega) (by omega)
    obtain ⟨b5, hb5⟩ := hinv.byte_present (a := (sRv.getReg rs1 + signExtend12 offset).toNat + 5)
      (by omega) (by omega)
    obtain ⟨b6, hb6⟩ := hinv.byte_present (a := (sRv.getReg rs1 + signExtend12 offset).toNat + 6)
      (by omega) (by omega)
    obtain ⟨b7, hb7⟩ := hinv.byte_present (a := (sRv.getReg rs1 + signExtend12 offset).toNat + 7)
      (by omega) (by omega)
    exact ⟨bm, sailInitMainMemoryRegion, b0, b1, b2, b3, b4, b5, b6, b7,
      hva, hm, sailInitMainMemoryRegion_readable, hpa, hcl, hsg, hht,
      hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩
  case LW rd rs1 offset =>
    simp only [stepSideCond, hfetch] at hside
    obtain ⟨ha1, ha2⟩ := hside
    have hv : isValidMemAccess (sRv.getReg rs1 + signExtend12 offset) = true := by
      by_contra hc
      exact hguard (step_lw_trap hfetch (by simpa using hc))
    have halign : (sRv.getReg rs1 + signExtend12 offset).toNat % 4 = 0 := by
      simp only [isValidMemAccess, Bool.and_eq_true, isAligned4, beq_iff_eq] at hv
      exact hv.2
    obtain ⟨bm, hreg, -⟩ := hinv.bare
    obtain ⟨hva, hm, hpa, hcl, hsg, -, hht⟩ := hinv.access_ok hlo hhi ha1 ha2 halign bm hreg
    obtain ⟨b0, hb0⟩ := hinv.byte_present (a := (sRv.getReg rs1 + signExtend12 offset).toNat)
      (by omega) (by omega)
    obtain ⟨b1, hb1⟩ := hinv.byte_present (a := (sRv.getReg rs1 + signExtend12 offset).toNat + 1)
      (by omega) (by omega)
    obtain ⟨b2, hb2⟩ := hinv.byte_present (a := (sRv.getReg rs1 + signExtend12 offset).toNat + 2)
      (by omega) (by omega)
    obtain ⟨b3, hb3⟩ := hinv.byte_present (a := (sRv.getReg rs1 + signExtend12 offset).toNat + 3)
      (by omega) (by omega)
    exact ⟨bm, sailInitMainMemoryRegion, b0, b1, b2, b3,
      hva, hm, sailInitMainMemoryRegion_readable, hpa, hcl, hsg, hht, hb0, hb1, hb2, hb3⟩
  case LWU rd rs1 offset =>
    simp only [stepSideCond, hfetch] at hside
    obtain ⟨ha1, ha2⟩ := hside
    have hv : isValidMemAccess (sRv.getReg rs1 + signExtend12 offset) = true := by
      by_contra hc
      exact hguard (step_lwu_trap hfetch (by simpa using hc))
    have halign : (sRv.getReg rs1 + signExtend12 offset).toNat % 4 = 0 := by
      simp only [isValidMemAccess, Bool.and_eq_true, isAligned4, beq_iff_eq] at hv
      exact hv.2
    obtain ⟨bm, hreg, -⟩ := hinv.bare
    obtain ⟨hva, hm, hpa, hcl, hsg, -, hht⟩ := hinv.access_ok hlo hhi ha1 ha2 halign bm hreg
    obtain ⟨b0, hb0⟩ := hinv.byte_present (a := (sRv.getReg rs1 + signExtend12 offset).toNat)
      (by omega) (by omega)
    obtain ⟨b1, hb1⟩ := hinv.byte_present (a := (sRv.getReg rs1 + signExtend12 offset).toNat + 1)
      (by omega) (by omega)
    obtain ⟨b2, hb2⟩ := hinv.byte_present (a := (sRv.getReg rs1 + signExtend12 offset).toNat + 2)
      (by omega) (by omega)
    obtain ⟨b3, hb3⟩ := hinv.byte_present (a := (sRv.getReg rs1 + signExtend12 offset).toNat + 3)
      (by omega) (by omega)
    exact ⟨bm, sailInitMainMemoryRegion, b0, b1, b2, b3,
      hva, hm, sailInitMainMemoryRegion_readable, hpa, hcl, hsg, hht, hb0, hb1, hb2, hb3⟩
  case LH rd rs1 offset =>
    simp only [stepSideCond, hfetch] at hside
    obtain ⟨ha1, ha2⟩ := hside
    have hv : isValidHalfwordAccess (sRv.getReg rs1 + signExtend12 offset) = true := by
      by_contra hc
      exact hguard (step_lh_trap hfetch (by simpa using hc))
    have halign : (sRv.getReg rs1 + signExtend12 offset).toNat % 2 = 0 := by
      simp only [isValidHalfwordAccess, Bool.and_eq_true, isAligned2, beq_iff_eq] at hv
      exact hv.2
    obtain ⟨bm, hreg, -⟩ := hinv.bare
    obtain ⟨hva, hm, hpa, hcl, hsg, -, hht⟩ := hinv.access_ok hlo hhi ha1 ha2 halign bm hreg
    obtain ⟨b0, hb0⟩ := hinv.byte_present (a := (sRv.getReg rs1 + signExtend12 offset).toNat)
      (by omega) (by omega)
    obtain ⟨b1, hb1⟩ := hinv.byte_present (a := (sRv.getReg rs1 + signExtend12 offset).toNat + 1)
      (by omega) (by omega)
    exact ⟨bm, sailInitMainMemoryRegion, b0, b1,
      hva, hm, sailInitMainMemoryRegion_readable, hpa, hcl, hsg, hht, hb0, hb1⟩
  case LHU rd rs1 offset =>
    simp only [stepSideCond, hfetch] at hside
    obtain ⟨ha1, ha2⟩ := hside
    have hv : isValidHalfwordAccess (sRv.getReg rs1 + signExtend12 offset) = true := by
      by_contra hc
      exact hguard (step_lhu_trap hfetch (by simpa using hc))
    have halign : (sRv.getReg rs1 + signExtend12 offset).toNat % 2 = 0 := by
      simp only [isValidHalfwordAccess, Bool.and_eq_true, isAligned2, beq_iff_eq] at hv
      exact hv.2
    obtain ⟨bm, hreg, -⟩ := hinv.bare
    obtain ⟨hva, hm, hpa, hcl, hsg, -, hht⟩ := hinv.access_ok hlo hhi ha1 ha2 halign bm hreg
    obtain ⟨b0, hb0⟩ := hinv.byte_present (a := (sRv.getReg rs1 + signExtend12 offset).toNat)
      (by omega) (by omega)
    obtain ⟨b1, hb1⟩ := hinv.byte_present (a := (sRv.getReg rs1 + signExtend12 offset).toNat + 1)
      (by omega) (by omega)
    exact ⟨bm, sailInitMainMemoryRegion, b0, b1,
      hva, hm, sailInitMainMemoryRegion_readable, hpa, hcl, hsg, hht, hb0, hb1⟩
  case LB rd rs1 offset =>
    simp only [stepSideCond, hfetch] at hside
    obtain ⟨ha1, ha2⟩ := hside
    obtain ⟨bm, hreg, -⟩ := hinv.bare
    obtain ⟨hva, hm, hpa, hcl, hsg, -, hht⟩ :=
      hinv.access_ok hlo hhi ha1 ha2 (Nat.mod_one _) bm hreg
    obtain ⟨b0, hb0⟩ := hinv.byte_present (a := (sRv.getReg rs1 + signExtend12 offset).toNat)
      (by omega) (by omega)
    exact ⟨bm, sailInitMainMemoryRegion, b0,
      hva, hm, sailInitMainMemoryRegion_readable, hpa, hcl, hsg, hht, hb0⟩
  case LBU rd rs1 offset =>
    simp only [stepSideCond, hfetch] at hside
    obtain ⟨ha1, ha2⟩ := hside
    obtain ⟨bm, hreg, -⟩ := hinv.bare
    obtain ⟨hva, hm, hpa, hcl, hsg, -, hht⟩ :=
      hinv.access_ok hlo hhi ha1 ha2 (Nat.mod_one _) bm hreg
    obtain ⟨b0, hb0⟩ := hinv.byte_present (a := (sRv.getReg rs1 + signExtend12 offset).toNat)
      (by omega) (by omega)
    exact ⟨bm, sailInitMainMemoryRegion, b0,
      hva, hm, sailInitMainMemoryRegion_readable, hpa, hcl, hsg, hht, hb0⟩
  case SD rs1 rs2 offset =>
    simp only [stepSideCond, hfetch] at hside
    obtain ⟨ha1, ha2⟩ := hside
    have hv : isValidDwordAccess (sRv.getReg rs1 + signExtend12 offset) = true := by
      by_contra hc
      exact hguard (step_sd_trap hfetch (by simpa using hc))
    have halign : (sRv.getReg rs1 + signExtend12 offset).toNat % 8 = 0 := by
      simp only [isValidDwordAccess, Bool.and_eq_true, isAligned8, beq_iff_eq] at hv
      exact hv.2
    obtain ⟨bm, hreg, -⟩ := hinv.bare
    obtain ⟨hva, hm, hpa, hcl, hsg, hht, -⟩ := hinv.access_ok hlo hhi ha1 ha2 halign bm hreg
    exact ⟨bm, sailInitMainMemoryRegion,
      hva, hm, sailInitMainMemoryRegion_writable, hpa, hcl, hsg, hht⟩
  case SW rs1 rs2 offset =>
    simp only [stepSideCond, hfetch] at hside
    obtain ⟨ha1, ha2⟩ := hside
    have hv : isValidMemAccess (sRv.getReg rs1 + signExtend12 offset) = true := by
      by_contra hc
      exact hguard (step_sw_trap hfetch (by simpa using hc))
    have halign : (sRv.getReg rs1 + signExtend12 offset).toNat % 4 = 0 := by
      simp only [isValidMemAccess, Bool.and_eq_true, isAligned4, beq_iff_eq] at hv
      exact hv.2
    obtain ⟨bm, hreg, -⟩ := hinv.bare
    obtain ⟨hva, hm, hpa, hcl, hsg, hht, -⟩ := hinv.access_ok hlo hhi ha1 ha2 halign bm hreg
    exact ⟨bm, sailInitMainMemoryRegion,
      hva, hm, sailInitMainMemoryRegion_writable, hpa, hcl, hsg, hht⟩
  case SH rs1 rs2 offset =>
    simp only [stepSideCond, hfetch] at hside
    obtain ⟨ha1, ha2⟩ := hside
    have hv : isValidHalfwordAccess (sRv.getReg rs1 + signExtend12 offset) = true := by
      by_contra hc
      exact hguard (step_sh_trap hfetch (by simpa using hc))
    have halign : (sRv.getReg rs1 + signExtend12 offset).toNat % 2 = 0 := by
      simp only [isValidHalfwordAccess, Bool.and_eq_true, isAligned2, beq_iff_eq] at hv
      exact hv.2
    obtain ⟨bm, hreg, -⟩ := hinv.bare
    obtain ⟨hva, hm, hpa, hcl, hsg, hht, -⟩ := hinv.access_ok hlo hhi ha1 ha2 halign bm hreg
    exact ⟨bm, sailInitMainMemoryRegion,
      hva, hm, sailInitMainMemoryRegion_writable, hpa, hcl, hsg, hht⟩
  case SB rs1 rs2 offset =>
    simp only [stepSideCond, hfetch] at hside
    obtain ⟨ha1, ha2⟩ := hside
    obtain ⟨bm, hreg, -⟩ := hinv.bare
    obtain ⟨hva, hm, hpa, hcl, hsg, hht, -⟩ :=
      hinv.access_ok hlo hhi ha1 ha2 (Nat.mod_one _) bm hreg
    exact ⟨bm, sailInitMainMemoryRegion,
      hva, hm, sailInitMainMemoryRegion_writable, hpa, hcl, hsg, hht⟩
  all_goals exact trivial

-- ============================================================================
-- One modelled step simulates one toy step
-- ============================================================================

/-- **One-step run-level simulation.**

    If the toy machine steps from `sRv` to `sRv'` on a run-simulable
    instruction, the modelled Sail step `sailStep si` retires successfully and
    the run-level invariant is re-established at the post-state.  **There is no
    `nextPC` hypothesis** — that is the point: `sailStep` installs the
    fetch-side default itself.

    ## Scope

    * **Simulable instructions only.** `ECALL`, `EBREAK`, `CSRS`, `FENCE` and the
      pseudo-instructions `MV`/`LI`/`NOP` are excluded (`toSailInstr?` maps them
      to `none`); the Sail model intentionally diverges from the toy model on
      syscalls and on the ZisK accelerator call.  `JALR` is excluded on top of
      that, because the vendored `update_elp_state` faults unconditionally — see
      `Instr.runSimulable` and `SailEquiv.update_elp_state_error`.
    * **RAM-zone memory only.** Accesses are confined to a caller-chosen window
      `[lo, hi) ⊆ [RAM_MEM_START, RAM_MEM_END) = [0xa0000000, 0xc0000000)`.  This
      is not laziness: the toy model's legacy MEM zone `[0x20, 0x78000000]` is
      **not inside any readable PMA region** of `sailInitPmaRegions` (whose
      main-memory region is `[0x80000000, 0x100000000)`), so the Sail-side
      access checks are simply false there and the side conditions are
      unprovable. -/
theorem sailStep_run_sim {lo hi : Nat} {sRv sRv' : MachineState} {sSail : SailState}
    {i : Instr} {si : SailInstr}
    (hinv : RunInv lo hi sRv sSail)
    (hlo : RAM_MEM_START ≤ lo) (hhi : hi ≤ RAM_MEM_END)
    (hfetch : sRv.code sRv.pc = some i) (hsim : i.runSimulable = true)
    (hsi : toSailInstr? i = some si) (hside : stepSideCond lo hi sRv)
    (hstep : step sRv = some sRv') :
    ∃ sSail', runSail (sailStep si) sSail = some ((), sSail') ∧ RunInv lo hi sRv' sSail' := by
  have hinvMid := hinv.insert_nextPC (sRv.pc + 4)
  have hnp :
      ({ sSail with regs := sSail.regs.insert Register.nextPC (sRv.pc + 4) } : SailState).regs.get?
        Register.nextPC = some (sRv.pc + 4) := by
    simp [Std.ExtDHashMap.get?_insert_self]
  have hsideI := instrSideCond_of_runInv hinvMid hlo hhi hfetch hsim hside (by rw [hstep]; simp)
  obtain ⟨sA, hexec, hrelA, hnpA, hfrA⟩ :=
    step_execute_sail_sim sRv _ hinvMid.toStateRelPC hnp i si hsi
      (Instr.simulable_of_runSimulable hsim) hsideI
  obtain ⟨sB, hstepB, hrelB, hfrB⟩ := step_of_execute hexec hrelA hnpA
  refine ⟨sB, ?_, ?_⟩
  · rw [runSail_sailStep_eq hinv.pc_agree]; exact hstepB
  · have hpost : sRv' = execInstrBr sRv i := step_eq_execInstrBr hfetch hsim hstep
    subst hpost
    exact hinv.reestablish
      ((platformFrame_insert_nextPC sSail _).trans (hfrA.trans hfrB)) hrelB

-- ============================================================================
-- Iterating the modelled step
-- ============================================================================

/-- `n` modelled Sail steps, driven by the toy machine's own instruction
    stream (the decode tie is out of scope, so the toy state supplies the
    instruction sequence).  Stops early if the toy machine traps or hits an
    unmapped instruction. -/
noncomputable def sailStepN : Nat → MachineState → SailM Unit
  | 0, _ => (Pure.pure () : SailM Unit)
  | n + 1, sRv =>
    match sRv.code sRv.pc >>= toSailInstr?, step sRv with
    | some si, some sRv' => sailStep si >>= fun _ => sailStepN n sRv'
    | _, _ => (Pure.pure () : SailM Unit)

/-- Unfolding lemma for a successful `sailStepN` step. -/
theorem sailStepN_succ_of {n : Nat} {sRv sRv' : MachineState} {si : SailInstr}
    (hsi : sRv.code sRv.pc >>= toSailInstr? = some si) (hstep : step sRv = some sRv') :
    sailStepN (n + 1) sRv = sailStep si >>= fun _ => sailStepN n sRv' := by
  simp only [sailStepN, hsi, hstep]

/-- **Run-level simulation.** `n` toy steps are matched by `n` modelled Sail
    steps, with the run-level invariant holding at every fetch boundary — in
    particular at the end.

    `hok` is the per-step obligation: at each intermediate state the fetched
    instruction is run-simulable and the toy-side side conditions of
    `stepSideCond` hold.  The same two scope restrictions as
    `sailStep_run_sim` apply (simulable-only; RAM-zone-only memory). -/
theorem sailStepN_run_sim (n : Nat) {lo hi : Nat} {sRv sRv' : MachineState} {sSail : SailState}
    (hinv : RunInv lo hi sRv sSail)
    (hlo : RAM_MEM_START ≤ lo) (hhi : hi ≤ RAM_MEM_END)
    (hrun : stepN n sRv = some sRv')
    (hok : ∀ k, k < n → ∀ sMid, stepN k sRv = some sMid →
      (∃ i, sMid.code sMid.pc = some i ∧ i.runSimulable = true) ∧ stepSideCond lo hi sMid) :
    ∃ sSail', runSail (sailStepN n sRv) sSail = some ((), sSail') ∧ RunInv lo hi sRv' sSail' := by
  induction n generalizing sRv sSail with
  | zero =>
    simp only [stepN_zero, Option.some.injEq] at hrun
    subst hrun
    exact ⟨sSail, by simp [sailStepN, runSail_pure], hinv⟩
  | succ m ih =>
    obtain ⟨⟨i, hfetch, hsim⟩, hside⟩ := hok 0 (Nat.succ_pos m) sRv (by simp)
    obtain ⟨si, hsi⟩ := toSailInstr?_isSome_of_simulable (Instr.simulable_of_runSimulable hsim)
    rw [stepN_succ] at hrun
    cases hstep : step sRv with
    | none => rw [hstep] at hrun; simp at hrun
    | some sMid =>
      rw [hstep] at hrun
      simp only [Option.bind_some] at hrun
      obtain ⟨sA, hsA, hinvA⟩ :=
        sailStep_run_sim hinv hlo hhi hfetch hsim hsi hside hstep
      have hok' : ∀ k, k < m → ∀ s, stepN k sMid = some s →
          (∃ j, s.code s.pc = some j ∧ j.runSimulable = true) ∧ stepSideCond lo hi s := by
        intro k hk s hs
        refine hok (k + 1) (by omega) s ?_
        rw [stepN_succ, hstep]
        simpa using hs
      obtain ⟨sB, hsB, hinvB⟩ := ih hinvA hrun hok'
      refine ⟨sB, ?_, hinvB⟩
      rw [sailStepN_succ_of (by rw [hfetch]; simpa using hsi) hstep, runSail_bind, hsA]
      exact hsB

end SailEquiv
end EvmAsm.Rv64
