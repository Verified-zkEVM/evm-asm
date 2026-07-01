/-
  EvmAsm.Rv64.SAsm.BlockSound

  Soundness of the SAsm block engine: a straight-line block of supported
  instructions satisfies a bounded CPS triple moving `regFileIs rf` to
  `regFileIs (execBlock rf instrs)`, under the block's own `CodeReq.ofProg`.

  The bridge is one generic per-instruction lemma (`regFile_alu_spec_within`)
  driven by three case-analysis facts about `aluSem`:
  - `aluSem_exec`: the classified result function mirrors `execInstrBr`;
  - `aluSem_agree`: the result function reads only the classified sources;
  - `aluSem_not_special`: classified instructions step via `execInstrBr`.

  Design: docs/sasm-design.md §3.4 (Milestone M2).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SAsm.Sym
import EvmAsm.Rv64.SAsm.RegFileSep
import EvmAsm.Rv64.SAsm.RegionSound

namespace EvmAsm.Rv64
namespace SAsm

-- ============================================================================
-- Bridges from aluSem to the machine semantics
-- ============================================================================

/-- The classified result function mirrors `execInstrBr` case-for-case. -/
theorem aluSem_exec {i : Instr} {op : AluOp} (h : aluSem i = some op) :
    ∀ s : MachineState,
      execInstrBr s i = (s.setReg op.rd (op.f s.getReg)).setPC (s.pc + 4) := by
  cases i <;> simp only [aluSem, reduceCtorEq] at h <;>
    (injection h with h; subst h; intro s; rfl)

/-- The classified result function depends only on the classified sources. -/
theorem aluSem_agree {i : Instr} {op : AluOp} (h : aluSem i = some op) :
    ∀ g g' : Reg → Word, (∀ r ∈ op.srcs, g r = g' r) → op.f g = op.f g' := by
  cases i <;> simp only [aluSem, reduceCtorEq] at h <;>
    (injection h with h; subst h; intro g g' hgg;
     simp only [List.forall_mem_cons] at hgg;
     first
       | (dsimp only; rw [hgg.1, hgg.2.1])
       | (dsimp only; rw [hgg.1])
       | dsimp only)

/-- Classified instructions are not ECALL/EBREAK and touch no memory, so they
    step via `execInstrBr`. -/
theorem aluSem_not_special {i : Instr} {op : AluOp} (h : aluSem i = some op) :
    i ≠ .ECALL ∧ i ≠ .EBREAK ∧ i.isMemAccess = false := by
  cases i <;> simp only [aluSem, reduceCtorEq] at h <;>
    exact ⟨by nofun, by nofun, rfl⟩

-- ============================================================================
-- Per-instruction and per-block CPS triples
-- ============================================================================

/-- Generic single-instruction spec at register-file granularity: one step,
    the whole exposed file moves from `rf` to `rf.set op.rd (op.f rf.get)`. -/
theorem regFile_alu_spec_within (i : Instr) (op : AluOp) (rf : RegFile) (base : Word)
    (hsem : aluSem i = some op)
    (hrd : (Reg.isExposed op.rd || op.rd == .x0) = true)
    (hsrcs : ∀ r ∈ op.srcs, (Reg.isExposed r || r == .x0) = true) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base i)
      (regFileIs rf)
      (regFileIs (rf.set op.rd (op.f rf.get))) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some i := CodeReq.singleton_satisfiedBy.mp hcr
  obtain ⟨hnec, hneb, hnm⟩ := aluSem_not_special hsem
  have hstep' : step s = some (execInstrBr s i) :=
    step_non_ecall_non_mem hfetch hnec hneb hnm
  have hexec' : execInstrBr s i = (s.setReg op.rd (op.f s.getReg)).setPC (s.pc + 4) :=
    aluSem_exec hsem s
  have hfagree : op.f s.getReg = op.f rf.get :=
    aluSem_agree hsem _ _ (fun r hr => holdsFor_regFileIs_agree hPR (hsrcs r hr))
  refine ⟨1, Nat.le_refl 1, (s.setReg op.rd (op.f s.getReg)).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · rw [hfagree]
    rcases Bool.or_eq_true_iff.mp hrd with hexp | hx0
    · exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_regFileIs _) hR)
        (holdsFor_sepConj_regFileIs_setReg hexp hPR)
    · have hx0' : op.rd = .x0 := by simpa using hx0
      rw [hx0', RegFile.set_x0]
      exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_regFileIs rf) hR) hPR

/-- Single-instruction spec, dispatched through `instrOk`/`execInstrRF`:
    ALU instructions leave the region framed; loads read from it. -/
theorem execInstrRF_sound {i : Instr} (reg : Region) (hreg : reg.wf)
    (hok : instrOk i = true)
    (rf : RegFile) (base : Word)
    (hvc : match loadSem i with
      | some l => reg.loadOk (rf.get l.rs1 + signExtend12 l.ofs) l.nbytes
      | none => True) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base i)
      ((regFileIs rf) ** bytesRegion reg.base reg.bytes)
      ((regFileIs (execInstrRF reg rf i)) ** bytesRegion reg.base reg.bytes) := by
  cases hsem : aluSem i with
  | none =>
      cases hload : loadSem i with
      | none => simp [instrOk, hsem, hload] at hok
      | some l =>
          simp only [instrOk, hsem, hload, Bool.and_eq_true] at hok
          simp only [hload] at hvc
          simp only [execInstrRF, hsem, hload]
          exact regFile_load_spec_within i l reg rf base hload hreg
            hok.1 hok.2 hvc
  | some op =>
      simp only [instrOk, hsem, Bool.and_eq_true] at hok
      obtain ⟨hrd, hsrcs⟩ := hok
      simp only [execInstrRF, hsem]
      exact cpsTripleWithin_frameR (bytesRegion reg.base reg.bytes)
        (bytesRegion_pcFree _ _)
        (regFile_alu_spec_within i op rf base hsem hrd
          (fun r hr => by
            have := List.all_eq_true.mp hsrcs r hr
            simpa using this))

/-- Block soundness: a supported straight-line block satisfies a bounded CPS
    triple under its own `CodeReq.ofProg`, moving the exposed register file
    to its symbolic image.  `hlen` rules out address wrap-around (any real
    block is vastly shorter). -/
theorem execBlock_sound (reg : Region) (instrs : List Instr) (rf : RegFile)
    (base : Word)
    (hreg : reg.wf) (hok : blockOk instrs = true)
    (hvcs : blockVCs reg rf instrs)
    (hlen : 4 * instrs.length < 2 ^ 64) :
    cpsTripleWithin instrs.length base (base + BitVec.ofNat 64 (4 * instrs.length))
      (CodeReq.ofProg base instrs)
      ((regFileIs rf) ** bytesRegion reg.base reg.bytes)
      ((regFileIs (execBlock reg rf instrs)) ** bytesRegion reg.base reg.bytes) := by
  induction instrs generalizing rf base with
  | nil =>
      intro R hR s hcr hPR hpc
      refine ⟨0, Nat.le_refl 0, s, rfl, ?_, hPR⟩
      simpa using hpc
  | cons i rest ih =>
      simp only [blockOk, List.all_cons, Bool.and_eq_true] at hok
      obtain ⟨hoki, hokr⟩ := hok
      obtain ⟨hvc1, hvcr⟩ := hvcs
      have hlenr : 4 * rest.length < 2 ^ 64 := by
        simp only [List.length_cons] at hlen; omega
      have h1 := execInstrRF_sound reg hreg hoki rf base hvc1
      have h2 := ih (execInstrRF reg rf i) (base + 4) hokr hvcr hlenr
      have hd : (CodeReq.singleton base i).Disjoint
          (CodeReq.ofProg (base + 4) rest) := by
        intro a
        by_cases ha : a = base
        · subst ha
          refine Or.inr (CodeReq.ofProg_none_range _ _ (fun k hk heq => ?_))
          have hk4 : 4 + 4 * k < 2 ^ 64 := by omega
          bv_omega
        · left
          simp [CodeReq.singleton, ha]
      have h3 := cpsTripleWithin_seq hd h1 h2
      rw [CodeReq.ofProg_cons]
      have hexit : (base + 4) + BitVec.ofNat 64 (4 * rest.length)
          = base + BitVec.ofNat 64 (4 * (rest.length + 1)) := by
        bv_omega
      rw [hexit] at h3
      simpa [List.length_cons, Nat.add_comm, execBlock_cons] using h3

end SAsm
end EvmAsm.Rv64
