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
    ALU instructions leave both regions framed; loads read from the region
    the routing condition selects, framing the other. -/
theorem execInstrRF_sound {i : Instr} (ro : Region) (rw : RwRegion)
    (hro : ro.wf) (hrw : rw.wf)
    (hok : instrOk i = true)
    (rf : RegFile) (ws : List (BitVec 8)) (hws : ws.length = rw.len)
    (base : Word)
    (hvc : match loadSem i with
      | some l =>
          if inRw rw.base ws (rf.get l.rs1 + signExtend12 l.ofs) l.nbytes
          then (Region.mk rw.base ws).loadOk
            (rf.get l.rs1 + signExtend12 l.ofs) l.nbytes
          else ro.loadOk (rf.get l.rs1 + signExtend12 l.ofs) l.nbytes
      | none =>
        match storeSem i with
        | some st =>
            inRw rw.base ws (rf.get st.rs1 + signExtend12 st.ofs) st.nbytes
              ∧ st.nbytes ∣ ((rf.get st.rs1 + signExtend12 st.ofs) - rw.base).toNat
        | none => True) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base i)
      ((regFileIs rf) ** (bytesRegion ro.base ro.bytes ** bytesRegion rw.base ws))
      ((regFileIs (execInstrRF ro rw.base rf ws i).1) **
        (bytesRegion ro.base ro.bytes **
          bytesRegion rw.base (execInstrRF ro rw.base rf ws i).2)) := by
  cases hsem : aluSem i with
  | none =>
      cases hload : loadSem i with
      | none =>
          cases hstore : storeSem i with
          | none => simp [instrOk, hsem, hload, hstore] at hok
          | some st =>
              simp only [instrOk, hsem, hload, hstore, Bool.and_eq_true] at hok
              simp only [hload, hstore] at hvc
              simp only [execInstrRF, hsem, hload, hstore]
              have hwf' : (Region.mk rw.base ws).wf := by
                refine ⟨hrw.1, ?_, ?_⟩
                · show rw.base.toNat + ws.length < 2 ^ 64
                  have := hrw.2.1
                  omega
                · intro k hk
                  have hk' : k < ws.length := hk
                  exact hrw.2.2 k (by omega)
              have h := regFile_store_spec_within i st rw.base rf ws base
                hstore hwf' hok.1 hok.2 hvc.1 hvc.2
              have h' := cpsTripleWithin_frameR (bytesRegion ro.base ro.bytes)
                (bytesRegion_pcFree _ _) h
              exact cpsTripleWithin_weaken (fun hp hh => sc_to_swap hp hh)
                (fun hp hh => sc_from_swap hp hh) h'
      | some l =>
          simp only [instrOk, hsem, hload, Bool.and_eq_true] at hok
          simp only [hload] at hvc
          simp only [execInstrRF, hsem, hload]
          by_cases hroute : inRw rw.base ws (rf.get l.rs1 + signExtend12 l.ofs) l.nbytes
          · rw [if_pos hroute] at hvc ⊢
            have hwf' : (Region.mk rw.base ws).wf := by
              refine ⟨hrw.1, ?_, ?_⟩
              · show rw.base.toNat + ws.length < 2 ^ 64
                have := hrw.2.1
                omega
              · intro k hk
                have hk' : k < ws.length := hk
                exact hrw.2.2 k (by omega)
            have h := regFile_load_spec_within i l (Region.mk rw.base ws) rf base
              hload hwf' hok.1 hok.2 hvc
            have h' := cpsTripleWithin_frameR (bytesRegion ro.base ro.bytes)
              (bytesRegion_pcFree _ _) h
            exact cpsTripleWithin_weaken (fun hp hh => sc_to_swap hp hh)
              (fun hp hh => sc_from_swap hp hh) h'
          · rw [if_neg hroute] at hvc ⊢
            have h := regFile_load_spec_within i l ro rf base
              hload hro hok.1 hok.2 hvc
            have h' := cpsTripleWithin_frameR (bytesRegion rw.base ws)
              (bytesRegion_pcFree _ _) h
            exact cpsTripleWithin_weaken (fun hp hh => sc_assoc_l hp hh)
              (fun hp hh => sc_assoc_r hp hh) h'
  | some op =>
      simp only [instrOk, hsem, Bool.and_eq_true] at hok
      obtain ⟨hrd, hsrcs⟩ := hok
      simp only [execInstrRF, hsem]
      exact cpsTripleWithin_frameR
        (bytesRegion ro.base ro.bytes ** bytesRegion rw.base ws)
        (pcFree_sepConj (bytesRegion_pcFree _ _) (bytesRegion_pcFree _ _))
        (regFile_alu_spec_within i op rf base hsem hrd
          (fun r hr => by
            have := List.all_eq_true.mp hsrcs r hr
            simpa using this))

/-- Block soundness: a supported straight-line block satisfies a bounded CPS
    triple under its own `CodeReq.ofProg`, moving the exposed register file
    and the writable region's contents to their symbolic image.  `hlen`
    rules out address wrap-around (any real block is vastly shorter). -/
theorem execBlock_sound (ro : Region) (rw : RwRegion) (instrs : List Instr)
    (rf : RegFile) (ws : List (BitVec 8)) (base : Word)
    (hro : ro.wf) (hrw : rw.wf) (hws : ws.length = rw.len)
    (hok : blockOk instrs = true)
    (hvcs : blockVCs ro rw.base rf ws instrs)
    (hlen : 4 * instrs.length < 2 ^ 64) :
    cpsTripleWithin instrs.length base (base + BitVec.ofNat 64 (4 * instrs.length))
      (CodeReq.ofProg base instrs)
      ((regFileIs rf) ** (bytesRegion ro.base ro.bytes ** bytesRegion rw.base ws))
      ((regFileIs (execBlock ro rw.base rf ws instrs).1) **
        (bytesRegion ro.base ro.bytes **
          bytesRegion rw.base (execBlock ro rw.base rf ws instrs).2)) := by
  induction instrs generalizing rf ws base with
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
      have h1 := execInstrRF_sound ro rw hro hrw hoki rf ws hws base hvc1
      have h2 := ih (execInstrRF ro rw.base rf ws i).1
        (execInstrRF ro rw.base rf ws i).2 (base + 4)
        (by rw [execInstrRF_ws_length]; exact hws)
        hokr hvcr hlenr
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
