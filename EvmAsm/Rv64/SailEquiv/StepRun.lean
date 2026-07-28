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

  The run-level tier is `Instr.simulable` — including `JALR`.  `JALR` was
  excluded from an earlier run-only predicate (`Instr.runSimulable`, now
  deleted) because the old extracted `currentlyEnabled` had no `Ext_Zicsr` arm,
  making `execute_JALR`'s leading `update_elp_state` fault in every state
  (#10688).  The regenerated model (tag 2026-07-27-9901550, `Zicsr_insts` in
  scope) fixed that arm; `update_elp_state_noop` (`RunInv.lean`) proves the call
  is a bare-mode no-op, `jalr_sideCond_of_runInv` below discharges the `JALR`
  side condition from the standard invariant, and `jalr_sideCond_satisfiable`
  exhibits a concrete witness pair — the constructive mirror of the old
  for-all-states unsatisfiability.
-/

import EvmAsm.Rv64.SailEquiv.RunInv
import EvmAsm.Rv64.SailEquiv.StepSim
import EvmAsm.Rv64.SailEquiv.StepProofs

open Out.Functions
open Sail

namespace EvmAsm.Rv64

namespace SailEquiv

/-- Every simulable instruction is mapped by `toSailInstr?`. -/
theorem toSailInstr?_isSome_of_simulable {i : Instr} (h : i.simulable = true) :
    ∃ si, toSailInstr? i = some si := by
  cases i <;> simp_all [Instr.simulable, toSailInstr?]

/-- A simulable instruction's `step` is exactly `execInstrBr`: the only
    `step` guards on this tier are the memory-access checks, and they can only
    turn success into `none`.  (`JALR` is on this tier: the toy `step` treats it
    as an ordinary non-memory instruction, via the catch-all
    `some i => some (execInstrBr s i)` arm.) -/
theorem step_eq_execInstrBr {s s' : MachineState} {i : Instr}
    (hfetch : s.code s.pc = some i) (hsim : i.simulable = true)
    (hstep : step s = some s') : s' = execInstrBr s i := by
  cases i
  case ECALL => exact absurd hsim (by simp [Instr.simulable])
  case EBREAK => exact absurd hsim (by simp [Instr.simulable])
  case FENCE => exact absurd hsim (by simp [Instr.simulable])
  case CSRS _ _ => exact absurd hsim (by simp [Instr.simulable])
  case MV _ _ => exact absurd hsim (by simp [Instr.simulable])
  case LI _ _ => exact absurd hsim (by simp [Instr.simulable])
  case NOP => exact absurd hsim (by simp [Instr.simulable])
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

/-- **The `JALR` side condition holds in every run-invariant state** — the
    constructive mirror of the #10688 defect.

    Before the 2026-07-27-9901550 model regen, `¬ instrSideCond (.JALR ..)` was
    provable for **all** states (the extracted `currentlyEnabled` had no
    `Ext_Zicsr` arm, so the `update_elp_state` conjunct was unsatisfiable and
    `jalr_sail_equiv` was vacuous).  This theorem shows the fixed model's side
    condition is dischargeable from the standard run-level invariant: the
    mid-state witness is `sSail` itself, because `update_elp_state_noop` shows
    the Zicfilp bookkeeping is a bare-mode no-op.

    `h_nextpc` is extra to `RunInv` (which deliberately carries no `nextPC`
    fact): the `JALR` side condition inspects `nextPC`, which is only pinned
    *post-fetch*, after `sailStep` installs the `pc + 4` default. -/
theorem jalr_sideCond_of_runInv {lo hi : Nat} {sRv : MachineState} {sSail : SailState}
    {rd rs1 : Reg} {offset : BitVec 12}
    (hinv : RunInv lo hi sRv sSail)
    (h_nextpc : sSail.regs.get? Register.nextPC = some (sRv.pc + 4))
    (h_align : ((sRv.getReg rs1 + signExtend12 offset) &&& ~~~1#64) &&& 3 = 0) :
    instrSideCond (.JALR rd rs1 offset) sRv sSail := by
  obtain ⟨bm, -, hmlpe⟩ := hinv.bare
  exact ⟨⟨sSail, update_elp_state_noop _ sSail bm.h_priv bm.h_sec hmlpe,
    hinv.toStateRel, hinv.pc_agree, h_nextpc, hinv.misa_present, PlatformFrame.refl _⟩, h_align⟩

/-- **The run-level invariant discharges every per-instruction Sail side
    condition.** Alignment comes from the toy `isValid*Access` guard (which
    `hguard` witnesses), window membership from `stepSideCond`, and everything
    else from `RunInv` itself.

    `h_nextpc` is consumed by the `JALR` arm alone (its side condition inspects
    `nextPC`, which `RunInv` deliberately does not constrain); the sole caller,
    `sailStep_run_sim`, applies this theorem at the post-fetch state where the
    `nextPC := pc + 4` default has just been installed, so the fact is free
    there. -/
theorem instrSideCond_of_runInv {lo hi : Nat} {sRv : MachineState} {sSail : SailState}
    {i : Instr} (hinv : RunInv lo hi sRv sSail)
    (h_nextpc : sSail.regs.get? Register.nextPC = some (sRv.pc + 4))
    (hlo : RAM_MEM_START ≤ lo) (hhi : hi ≤ RAM_MEM_END)
    (hfetch : sRv.code sRv.pc = some i) (hsim : i.simulable = true)
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
    simp only [stepSideCond, hfetch] at hside
    exact jalr_sideCond_of_runInv hinv h_nextpc hside
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
    exact ⟨bm, sailInitMainMemoryRegion,
      hva, hm, sailInitMainMemoryRegion_readable, hpa, hcl, hsg, hht,
      hinv.mem_present.bytesPresent ha1 ha2⟩
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
    exact ⟨bm, sailInitMainMemoryRegion,
      hva, hm, sailInitMainMemoryRegion_readable, hpa, hcl, hsg, hht,
      hinv.mem_present.bytesPresent ha1 ha2⟩
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
    exact ⟨bm, sailInitMainMemoryRegion,
      hva, hm, sailInitMainMemoryRegion_readable, hpa, hcl, hsg, hht,
      hinv.mem_present.bytesPresent ha1 ha2⟩
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
    exact ⟨bm, sailInitMainMemoryRegion,
      hva, hm, sailInitMainMemoryRegion_readable, hpa, hcl, hsg, hht,
      hinv.mem_present.bytesPresent ha1 ha2⟩
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
    exact ⟨bm, sailInitMainMemoryRegion,
      hva, hm, sailInitMainMemoryRegion_readable, hpa, hcl, hsg, hht,
      hinv.mem_present.bytesPresent ha1 ha2⟩
  case LB rd rs1 offset =>
    simp only [stepSideCond, hfetch] at hside
    obtain ⟨ha1, ha2⟩ := hside
    obtain ⟨bm, hreg, -⟩ := hinv.bare
    obtain ⟨hva, hm, hpa, hcl, hsg, -, hht⟩ :=
      hinv.access_ok hlo hhi ha1 ha2 (Nat.mod_one _) bm hreg
    exact ⟨bm, sailInitMainMemoryRegion,
      hva, hm, sailInitMainMemoryRegion_readable, hpa, hcl, hsg, hht,
      hinv.mem_present.bytesPresent ha1 ha2⟩
  case LBU rd rs1 offset =>
    simp only [stepSideCond, hfetch] at hside
    obtain ⟨ha1, ha2⟩ := hside
    obtain ⟨bm, hreg, -⟩ := hinv.bare
    obtain ⟨hva, hm, hpa, hcl, hsg, -, hht⟩ :=
      hinv.access_ok hlo hhi ha1 ha2 (Nat.mod_one _) bm hreg
    exact ⟨bm, sailInitMainMemoryRegion,
      hva, hm, sailInitMainMemoryRegion_readable, hpa, hcl, hsg, hht,
      hinv.mem_present.bytesPresent ha1 ha2⟩
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

    If the toy machine steps from `sRv` to `sRv'` on a simulable instruction,
    the modelled Sail step `sailStep si` retires successfully and
    the run-level invariant is re-established at the post-state.  **There is no
    `nextPC` hypothesis** — that is the point: `sailStep` installs the
    fetch-side default itself.

    ## Scope

    * **Simulable instructions only.** `ECALL`, `EBREAK`, `CSRS`, `FENCE` and the
      pseudo-instructions `MV`/`LI`/`NOP` are excluded (`toSailInstr?` maps them
      to `none`); the Sail model intentionally diverges from the toy model on
      syscalls and on the ZisK accelerator call.  `JALR` **is** covered: its
      historical exclusion (#10688 — the pre-regen model's `update_elp_state`
      faulted in every state) is resolved by `update_elp_state_noop` /
      `jalr_sideCond_of_runInv`.
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
    (hfetch : sRv.code sRv.pc = some i) (hsim : i.simulable = true)
    (hsi : toSailInstr? i = some si) (hside : stepSideCond lo hi sRv)
    (hstep : step sRv = some sRv') :
    ∃ sSail', runSail (sailStep si) sSail = some ((), sSail') ∧ RunInv lo hi sRv' sSail' := by
  have hinvMid := hinv.insert_nextPC (sRv.pc + 4)
  have hnp :
      ({ sSail with regs := sSail.regs.insert Register.nextPC (sRv.pc + 4) } : SailState).regs.get?
        Register.nextPC = some (sRv.pc + 4) := by
    simp [Std.ExtDHashMap.get?_insert_self]
  have hsideI :=
    instrSideCond_of_runInv hinvMid hnp hlo hhi hfetch hsim hside (by rw [hstep]; simp)
  obtain ⟨sA, hexec, hrelA, hnpA, hfrA⟩ :=
    step_execute_sail_sim sRv _ hinvMid.toStateRelPC hnp i si hsi hsim hsideI
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
    instruction is simulable and the toy-side side conditions of
    `stepSideCond` hold.  The same two scope restrictions as
    `sailStep_run_sim` apply (simulable-only; RAM-zone-only memory). -/
theorem sailStepN_run_sim (n : Nat) {lo hi : Nat} {sRv sRv' : MachineState} {sSail : SailState}
    (hinv : RunInv lo hi sRv sSail)
    (hlo : RAM_MEM_START ≤ lo) (hhi : hi ≤ RAM_MEM_END)
    (hrun : stepN n sRv = some sRv')
    (hok : ∀ k, k < n → ∀ sMid, stepN k sRv = some sMid →
      (∃ i, sMid.code sMid.pc = some i ∧ i.simulable = true) ∧ stepSideCond lo hi sMid) :
    ∃ sSail', runSail (sailStepN n sRv) sSail = some ((), sSail') ∧ RunInv lo hi sRv' sSail' := by
  induction n generalizing sRv sSail with
  | zero =>
    simp only [stepN_zero, Option.some.injEq] at hrun
    subst hrun
    exact ⟨sSail, by simp [sailStepN, runSail_pure], hinv⟩
  | succ m ih =>
    obtain ⟨⟨i, hfetch, hsim⟩, hside⟩ := hok 0 (Nat.succ_pos m) sRv (by simp)
    obtain ⟨si, hsi⟩ := toSailInstr?_isSome_of_simulable hsim
    rw [stepN_succ] at hrun
    cases hstep : step sRv with
    | none => rw [hstep] at hrun; simp at hrun
    | some sMid =>
      rw [hstep] at hrun
      simp only [Option.bind_some] at hrun
      obtain ⟨sA, hsA, hinvA⟩ :=
        sailStep_run_sim hinv hlo hhi hfetch hsim hsi hside hstep
      have hok' : ∀ k, k < m → ∀ s, stepN k sMid = some s →
          (∃ j, s.code s.pc = some j ∧ j.simulable = true) ∧ stepSideCond lo hi s := by
        intro k hk s hs
        refine hok (k + 1) (by omega) s ?_
        rw [stepN_succ, hstep]
        simpa using hs
      obtain ⟨sB, hsB, hinvB⟩ := ih hinvA hrun hok'
      refine ⟨sB, ?_, hinvB⟩
      rw [sailStepN_succ_of (by rw [hfetch]; simpa using hsi) hstep, runSail_bind, hsA]
      exact hsB

-- ============================================================================
-- Absolute satisfiability of the JALR side condition (#10688 anti-vacuity)
-- ============================================================================

/-- Toy-side witness for `jalr_sideCond_satisfiable`: the all-zero machine
    (every register `0`, every memory dword `0`, `pc = 0`, no code mapped). -/
def jalrWitnessRvState : MachineState :=
  { regs := fun _ => 0#64, mem := fun _ => 0#64, pc := 0#64 }

/-- Sail-side witness for `jalr_sideCond_satisfiable`: all 32 integer registers
    zeroed (matching `jalrWitnessRvState` under `StateRel`), `cur_privilege =
    Machine` and `mseccfg = 0` (so `update_elp_state` is a no-op by
    `update_elp_state_noop`), `misa = 0` (merely present, as the side condition
    requires), `PC = 0` and `nextPC = 4` (the post-fetch default), and empty
    byte memory (which reconstructs to the toy's all-zero dwords). -/
def jalrWitnessSailState : SailState :=
  { (default : SailState) with
    regs :=
      (((((((((((((((((((((((((((((((((((
        (default : SailState).regs.insert Register.x1 0#64).insert
        Register.x2 0#64).insert Register.x3 0#64).insert Register.x4 0#64).insert
        Register.x5 0#64).insert Register.x6 0#64).insert Register.x7 0#64).insert
        Register.x8 0#64).insert Register.x9 0#64).insert Register.x10 0#64).insert
        Register.x11 0#64).insert Register.x12 0#64).insert Register.x13 0#64).insert
        Register.x14 0#64).insert Register.x15 0#64).insert Register.x16 0#64).insert
        Register.x17 0#64).insert Register.x18 0#64).insert Register.x19 0#64).insert
        Register.x20 0#64).insert Register.x21 0#64).insert Register.x22 0#64).insert
        Register.x23 0#64).insert Register.x24 0#64).insert Register.x25 0#64).insert
        Register.x26 0#64).insert Register.x27 0#64).insert Register.x28 0#64).insert
        Register.x29 0#64).insert Register.x30 0#64).insert Register.x31 0#64).insert
        Register.cur_privilege Privilege.Machine).insert
        Register.mseccfg 0#64).insert Register.misa 0#64).insert
        Register.PC 0#64).insert Register.nextPC 4#64 }

/-- **The `JALR` side condition is satisfiable** — for every choice of `rd` and
    `rs1`, a concrete state pair witnesses `instrSideCond (.JALR rd rs1 0)`.

    This is the absolute-satisfiability mirror of #10688: under the pre-regen
    vendored model, `¬ instrSideCond (.JALR rd rs1 offset) sRv sSail` was
    provable for **all** states (so `jalr_sail_equiv`, `jalr_step_sail_equiv`
    and the `.JALR` arm of `step_execute_sail_sim` were vacuously true).  With
    the `Ext_Zicsr` arm restored, the witness below discharges every conjunct
    constructively; offset `0` with an all-zero register file satisfies the
    `(target &&& ~~~1) &&& 3 = 0` alignment conjunct.  The relative form —
    every `RunInv` state qualifies — is `jalr_sideCond_of_runInv`. -/
theorem jalr_sideCond_satisfiable (rd rs1 : Reg) :
    ∃ (sRv : MachineState) (sSail : SailState),
      instrSideCond (.JALR rd rs1 (0 : BitVec 12)) sRv sSail := by
  refine ⟨jalrWitnessRvState, jalrWitnessSailState,
    ⟨jalrWitnessSailState,
      update_elp_state_noop _ _ (msec := 0#64) ?_ ?_ (by decide),
      ⟨?_, ?_⟩, ?_, ?_, ⟨0#64, ?_⟩, PlatformFrame.refl _⟩, ?_⟩
  · simp [jalrWitnessSailState, Std.ExtDHashMap.get?_insert]
  · simp [jalrWitnessSailState, Std.ExtDHashMap.get?_insert]
  · intro r
    cases r <;>
      simp [sailRegVal, jalrWitnessSailState, jalrWitnessRvState, MachineState.getReg,
        Std.ExtDHashMap.get?_insert]
  · intro a ha
    show reconstructDword (default : SailState).mem a.toNat = jalrWitnessRvState.getMem a
    have hd : ((default : SailState).mem : Std.ExtHashMap Nat (BitVec 8)) = ∅ := rfl
    simp [reconstructDword, hd, jalrWitnessRvState, MachineState.getMem]
  · simp [jalrWitnessSailState, jalrWitnessRvState, Std.ExtDHashMap.get?_insert]
  · simp [jalrWitnessSailState, jalrWitnessRvState]
  · simp [jalrWitnessSailState, Std.ExtDHashMap.get?_insert]
  · cases rs1 <;> simp [jalrWitnessRvState, MachineState.getReg] <;> decide

end SailEquiv
end EvmAsm.Rv64
